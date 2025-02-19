import subprocess
import enum

from typing import cast

from c2po import cpt, log, util, types, options

MODULE_CODE = "SAT"

PREAMBLE = f"""(set-info :source |SMT encoding for satisfiability checking of Mission-time Linear Temporal Logic (MLTL) formulas.\nEncoded by C2PO v{log.VERSION}, see https://github.com/R2U2/r2u2/tree/develop/compiler.|)"""


class SatResult(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"
    FAILURE = "fail"


def check_solver() -> bool:
    try:
        proc0 = subprocess.run([options.smt_solver, "-version"], capture_output=True)
        proc1 = subprocess.run([options.smt_solver, "--version"], capture_output=True)
        return proc0.returncode == 0 or proc1.returncode == 0
    except FileNotFoundError:
        return False


def run_smt_solver(smt: str, timeout: float) -> tuple[SatResult, float]:
    """Runs the SMT solver on the given SMT-LIB2 encoding and returns the result."""
    log.debug(MODULE_CODE, 1, "Running SMT solver.")

    if not check_solver():
        log.error(MODULE_CODE, f"{options.smt_solver} not found")
        return (SatResult.FAILURE, -1)

    smt_file_path = options.workdir / "__tmp__.smt"
    with open(smt_file_path, "w") as f:
        f.write(smt)

    command = [options.smt_solver, str(smt_file_path)] + [opt.replace('"', '') for opt in options.smt_options]
    log.debug(MODULE_CODE, 1, f"Running '{' '.join(command)}'")

    try:
        start = util.get_rusage_time()
        proc = subprocess.run(command, capture_output=True, timeout=timeout)
        end = util.get_rusage_time()
    except subprocess.TimeoutExpired:
        log.warning(
            MODULE_CODE, f"{options.smt_solver} timeout after {timeout}s"
        )
        return (SatResult.TIMEOUT, -1)

    if proc.returncode != 0:
        log.error(
            MODULE_CODE,
            f"{options.smt_solver} failed with return code {proc.returncode}",
        )
        log.debug(MODULE_CODE, 1, proc.stdout.decode()[:-1])
        return (SatResult.FAILURE, -1)

    if proc.stdout.decode().find("unsat") > -1:
        log.debug(MODULE_CODE, 1, "unsat")
        result = SatResult.UNSAT
    elif proc.stdout.decode().find("sat") > -1:
        log.debug(MODULE_CODE, 1, "sat")
        result = SatResult.SAT
    else:
        log.debug(MODULE_CODE, 1, "unknown")
        result = SatResult.UNKNOWN

    sat_time = end - start
    return (result, sat_time)


def to_qfbv_smtlib2(start: cpt.Expression, context: cpt.Context, trace_len: int) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the QF_BV logic. Specifically, encodes whether there exists a trace of length at most `trace_len` that satisfies the formula."""
    log.debug(
        MODULE_CODE,
        1,
        f"Encoding MLTL formula in QF_BV logic (up to length {trace_len}):\n\t{repr(start)}",
    )

    bv_width = trace_len
    bv_sort = f"(_ BitVec {bv_width})"

    def to_bv(value: int):
        nonlocal bv_width
        return f"(_ bv{value} {bv_width})"

    def ones():
        nonlocal bv_width
        return f"(_ bv{2**bv_width - 1} {bv_width})"

    def zeros():
        nonlocal bv_width
        return f"(_ bv0 {bv_width})"

    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic QF_BV)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal in context.signals.keys():
        atomic_map[signal] = f"f_{signal}"
        smt_commands.append(f"(declare-fun f_{signal} () {bv_sort})")

    unrolled_expr = cpt.unroll_temporal_operators(start, context)
    for expr in cpt.postorder(unrolled_expr, context):
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        if expr.type != types.BoolType():
            log.error(MODULE_CODE, f"Unsupported type {expr.type} ({expr})")
            return ""

        fun_signature = f"define-fun {expr_id} () {bv_sort} "

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature} {ones()})")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature} {zeros()})")
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(f"({fun_signature} {atomic_map[expr.symbol]})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (bvnot {expr_map[expr.children[0]]}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            op = f"(bvand {expr_map[expr.children[0]]} {expr_map[expr.children[1]]})"
            for child in expr.children[2:]:
                op = f"(bvand {op} {expr_map[child]})"
            smt_commands.append(f"({fun_signature} {op})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            op = f"(bvor {expr_map[expr.children[0]]} {expr_map[expr.children[1]]})"
            for child in expr.children[2:]:
                op = f"(bvor {op} {expr_map[child]})"
            smt_commands.append(f"({fun_signature} {op})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (bvxnor {expr_map[expr.children[0]]} {expr_map[expr.children[1]]}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            # We want to implement the following:
            # cs(G[lb,lb] p) := cs(p) << lb where we shift in ones from the right
            # To do so, we shift by lb and then OR with a bitmask of 1s equal to 2^lb - 1
            # Example: let cs(p) = 0b1010 and lb = 2, then cs(G[2,2] p) = (0b1010 << 2) | 0b0011 = 0b1011
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            shift_amt = f"(_ bv{lb} {bv_width})"
            shift_ones_bitmask = f"(_ bv{2**lb - 1} {bv_width})"
            smt_commands.append(
                f"({fun_signature} (bvor (bvshl {expr_map[expr.children[0]]} {shift_amt}) {shift_ones_bitmask}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            shift_amt = f"(_ bv{lb} {bv_width})"
            smt_commands.append(
                f"({fun_signature} (bvshl {expr_map[expr.children[0]]} {shift_amt}))"
            )
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append(f"(assert (bvugt {expr_map[unrolled_expr]} {zeros()}))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def check_sat_qfbv_incr(start: cpt.Expression, context: cpt.Context) -> SatResult:
    """Incrementally searches for an int `len` up to `start.wpd` such that `check_sat(to_qfbv_smtlib2(start, context, len))` is not unknown."""
    total_sat_time: float = 0
    num_sat_calls: int = 0
    trace_len: int = 1

    def update_stats(sat_time: float) -> None:
        nonlocal total_sat_time, num_sat_calls, trace_len
        total_sat_time += sat_time
        num_sat_calls += 1
        log.stat(MODULE_CODE, f"sat_time_{num_sat_calls}={sat_time}")
        log.stat(MODULE_CODE, f"sat_trace_len_{num_sat_calls}={trace_len}")

    def report_stats(result: SatResult) -> None:
        nonlocal total_sat_time, num_sat_calls
        log.stat(MODULE_CODE, f"sat_result={result.value}")
        log.stat(MODULE_CODE, f"num_sat_calls={num_sat_calls}")
        log.stat(MODULE_CODE, f"sat_time={total_sat_time}")

    def done(result: SatResult) -> bool:
        # We know we are done when the result is sat, timeout, or failure or we have checked traces with length up to start.wpd + 1
        nonlocal trace_len
        return result in {SatResult.SAT, SatResult.TIMEOUT, SatResult.FAILURE} or trace_len >= (start.wpd + 1)

    log.debug(
        MODULE_CODE,
        1,
        f"Checking satisfiability of MLTL formula in QF_BV logic:\n\t{repr(start)}",
    )

    if options.enable_booleanizer:
        log.warning(
            MODULE_CODE,
            "Booleanizer enabled, skipping QF_BV sat check.\n\t"
            "Consider using a different SMT theory.",
        )
        return SatResult.UNKNOWN

    # start with a quick check
    smt = to_qfbv_smtlib2(start, context, trace_len)
    (result, sat_time) = run_smt_solver(smt, options.timeout_sat)
    update_stats(sat_time)
    if done(result):
        report_stats(result)
        return result

    # if wpd is less than 256 then just go straight for it
    if start.wpd <= 255:
        trace_len = start.wpd - 1
        smt = to_qfbv_smtlib2(start, context, trace_len)
        (result, sat_time) = run_smt_solver(smt, options.timeout_sat - total_sat_time)
        update_stats(sat_time)
        report_stats(result)
        return result

    # otherwise wpd >= 256, so try its bpd first, then its wpd
    trace_len = start.bpd + 1
    smt = to_qfbv_smtlib2(start, context, trace_len)
    (result, sat_time) = run_smt_solver(smt, options.timeout_sat - total_sat_time)
    update_stats(sat_time)
    if done(result):
        report_stats(result)
        return result
    
    trace_len = start.wpd + 1
    smt = to_qfbv_smtlib2(start, context, trace_len)
    (result, sat_time) = run_smt_solver(smt, options.timeout_sat - total_sat_time)
    update_stats(sat_time)

    report_stats(result)
    return result


def to_qfaufbv_smtlib2(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the QF_AUFBV logic."""
    log.debug(
        MODULE_CODE, 1, f"Encoding MLTL formula in QF_AUFBV logic:\n\t{repr(start)}"
    )

    if options.mission_time > 0:
        mission_time = options.mission_time
    elif start.wpd > 0:
        mission_time = start.wpd
    else:
        mission_time = 1

    timestamp_width = mission_time.bit_length()
    timestamp_sort = f"(_ BitVec {timestamp_width})"

    def to_bv(value: int):
        nonlocal timestamp_width
        return f"(_ bv{value} {timestamp_width})"

    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic QF_AUFBV)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        if typ == types.BoolType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array {timestamp_sort} (_ BitVec 1)))"
            )
        elif typ == types.IntType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array {timestamp_sort} (_ BitVec {types.IntType().width})))"
            )

    for expr in cpt.postorder(start, context):
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        if expr.type == types.BoolType():
            smt_type = "Bool"
        elif expr.type == types.IntType():
            smt_type = f"(_ BitVec {types.IntType().width})"
        else:
            log.error(MODULE_CODE, f"Unsupported type {expr.type} ({expr})")
            return ""

        fun_signature = f"define-fun {expr_id} ((k {timestamp_sort}) (len {timestamp_sort})) {smt_type}"

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) true))")
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) false))")
        elif isinstance(expr, cpt.Constant):
            smt_commands.append(f"({fun_signature} (_ bv{expr.value} {types.IntType().width}))")
        elif isinstance(expr, cpt.Signal) and types.is_bool_type(expr.type):
            # Have to compare to #b1 because MathSat doesn't allow Arrays to have Bool elements
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= (select {atomic_map[expr.symbol]} k) #b1)))"
            )
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(
                f"({fun_signature} (select {atomic_map[expr.symbol]} k))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            smt_commands.append(
                f"({fun_signature} (bvadd ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
            smt_commands.append(
                f"({fun_signature} (bvsub ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            smt_commands.append(
                f"({fun_signature} (bvmul ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            op = "bvudiv" if not types.IntType().is_signed else "bvsdiv"
            smt_commands.append(
                f"({fun_signature} ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            op = "bvurem" if not types.IntType().is_signed else "bvsmod"
            smt_commands.append(
                f"({fun_signature} ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            smt_commands.append(
                f"({fun_signature} (bvneg ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            op = "bvugt" if not types.IntType().is_signed else "bvsgt"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            op = "bvuge" if not types.IntType().is_signed else "bvsge"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            op = "bvult" if not types.IntType().is_signed else "bvslt"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            op = "bvule" if not types.IntType().is_signed else "bvsle"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (bvugt len k) {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (or {operands})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            conds = [
                f"({expr_map[expr.children[0]]} (bvadd k (_ bv{i} {timestamp_width})) len)"
                for i in range(lb, ub + 1)
            ]
            smt_commands.append(
                f"({fun_signature} "
                f"(and (bvugt len k) (or (bvule len (bvadd {to_bv(lb)} k)) "
                f"(and {' '.join(conds)}))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            conds = [
                f"({expr_map[expr.children[0]]} (bvadd k (_ bv{i} {timestamp_width})) len)"
                for i in range(lb, ub + 1)
            ]
            smt_commands.append(
                f"({fun_signature} "
                f"(and (bvugt len (bvadd {to_bv(lb)} k)) "
                f"(or {' '.join(conds)})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub

            unroll = f"({expr_map[expr.children[1]]} (bvadd {to_bv(ub)} k) len)"
            for i in reversed(range(lb, ub)):
                unroll = f"(or ({expr_map[expr.children[1]]} (bvadd {to_bv(lb + i)} k) len) (and ({expr_map[expr.children[0]]} (bvadd {to_bv(lb + i)} k) len) {unroll}))"

            smt_commands.append(
                f"({fun_signature} (and (bvugt len (bvadd {to_bv(lb)} k)) {unroll}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                MODULE_CODE, f"Release not implemented for MLTL-SAT via QF_AUFBV\n\t{expr}"
            )
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append(f"(declare-fun len () {timestamp_sort})")
    smt_commands.append(f"(assert ({expr_map[start]} {to_bv(0)} len))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def to_aufbv_smtlib2(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the AUFBV logic."""
    log.debug(MODULE_CODE, 1, f"Encoding MLTL formula in AUFBV logic:\n\t{repr(start)}")

    if options.mission_time > 0:
        mission_time = options.mission_time
    elif start.wpd > 0:
        mission_time = start.wpd
    else:
        mission_time = 1

    timestamp_width = mission_time.bit_length()
    timestamp_sort = f"(_ BitVec {timestamp_width})"

    def to_bv(value: int):
        nonlocal timestamp_width
        return f"(_ bv{value} {timestamp_width})"

    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic AUFBV)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        if typ == types.BoolType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array {timestamp_sort} (_ BitVec 1)))"
            )
        elif typ == types.IntType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array {timestamp_sort} (_ BitVec {types.IntType().width})))"
            )

    for expr in cpt.postorder(start, context):
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        if expr.type == types.BoolType():
            smt_type = "Bool"
        elif expr.type == types.IntType():
            smt_type = f"(_ BitVec {types.IntType().width})"
        else:
            log.error(MODULE_CODE, f"Unsupported type {expr.type} ({expr})")
            return ""

        fun_signature = f"define-fun {expr_id} ((k {timestamp_sort}) (len {timestamp_sort})) {smt_type}"

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) true))")
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) false))")
        elif isinstance(expr, cpt.Constant):
            smt_commands.append(f"({fun_signature} (_ bv{expr.value} {types.IntType().width}))")
        elif isinstance(expr, cpt.Signal) and types.is_bool_type(expr.type):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= (select {atomic_map[expr.symbol]} k) #b1)))"
            )
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(
                f"({fun_signature} (select {atomic_map[expr.symbol]} k))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            smt_commands.append(
                f"({fun_signature} (bvadd ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
            smt_commands.append(
                f"({fun_signature} (bvsub ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            smt_commands.append(
                f"({fun_signature} (bvmul ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            op = "bvudiv" if not types.IntType().is_signed else "bvsdiv"
            smt_commands.append(
                f"({fun_signature} ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            op = "bvurem" if not types.IntType().is_signed else "bvsmod"
            smt_commands.append(
                f"({fun_signature} ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            smt_commands.append(
                f"({fun_signature} (bvneg ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            op = "bvugt" if not types.IntType().is_signed else "bvsgt"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            op = "bvuge" if not types.IntType().is_signed else "bvsge"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            op = "bvult" if not types.IntType().is_signed else "bvslt"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            op = "bvule" if not types.IntType().is_signed else "bvsle"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (bvugt len k) {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (or {operands})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k)  (or (bvule len (bvadd {to_bv(lb)} k)) (forall ((i {timestamp_sort})) (=> (and (bvule (bvadd {to_bv(lb)} k) i) (bvule i (bvadd {to_bv(ub)} k)) (bvult i len)) ({expr_map[expr.children[0]]} i len))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (bvugt len (bvadd {to_bv(lb)} k)) (exists ((i {timestamp_sort})) (and (bvule (bvadd {to_bv(lb)} k) i) (bvule i (bvadd {to_bv(ub)} k)) (bvult i len) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (bvugt len (bvadd {to_bv(lb)} k)) (exists ((i {timestamp_sort})) (and (bvule (bvadd {to_bv(lb)} k) i) (bvule i (bvadd {to_bv(ub)} k)) (bvult i len) ({expr_map[expr.children[1]]} i len) (forall ((j {timestamp_sort})) (=> (and (bvule (bvadd {to_bv(lb)} k) j) (bvult j i)) ({expr_map[expr.children[0]]} j len)))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                MODULE_CODE, f"Release not implemented for MLTL-SAT via AUFBV\n\t{expr}"
            )
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append(f"(declare-fun len () {timestamp_sort})")
    smt_commands.append(f"(assert ({expr_map[start]} {to_bv(0)} len))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def to_qfauflia_smtlib2(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the QF_AUFLIA logic."""
    log.debug(
        MODULE_CODE, 1, f"Encoding MLTL formula in QF_AUFLIA logic:\n\t{repr(start)}"
    )

    is_nonlinear: bool = False
    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic QF_AUFLIA)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        if typ == types.BoolType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array Int Bool))"
            )
        elif typ == types.IntType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array Int Int))"
            )

    for expr in cpt.postorder(start, context):
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        if expr.type == types.BoolType():
            smt_type = "Bool"
        elif expr.type == types.IntType():
            smt_type = "Int"
        else:
            log.error(MODULE_CODE, f"Unsupported type {expr.type} ({expr})")
            return ""

        fun_signature = f"define-fun {expr_id} ((k Int) (len Int)) {smt_type}"

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            smt_commands.append(f"({fun_signature} true)")
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            smt_commands.append(f"({fun_signature} false)")
        elif isinstance(expr, cpt.Constant):
            smt_commands.append(f"({fun_signature} {expr.value})")
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(
                f"({fun_signature} (select {atomic_map[expr.symbol]} k))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            smt_commands.append(
                f"({fun_signature} (+ ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (* ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (div ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (mod ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (>= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (< ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (<= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (> len k) {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and (> len k) (or {operands})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            conds = [
                f"({expr_map[expr.children[0]]} (+ k {i}) len)"
                for i in range(lb, ub + 1)
            ]
            smt_commands.append(
                f"({fun_signature} "
                f"(and (> len k) (or (<= len (+ {lb} k)) "
                f"(and {' '.join(conds)}))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            conds = [
                f"({expr_map[expr.children[0]]} (+ k {i}) len)"
                for i in range(lb, ub + 1)
            ]
            smt_commands.append(
                f"({fun_signature} "
                f"(and (> len (+ {lb} k)) "
                f"(or {' '.join(conds)})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub

            unroll = f"({expr_map[expr.children[1]]} (+ {ub} k) len)"
            for i in reversed(range(lb, ub)):
                unroll = f"(or ({expr_map[expr.children[1]]} (+ {lb + i} k) len) (and ({expr_map[expr.children[0]]} (+ {lb + i} k) len) {unroll}))"

            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) {unroll}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                MODULE_CODE, f"Release not implemented for MLTL-SAT via QF_AUFLIA\n\t{expr}"
            )
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append("(declare-fun len () Int)")
    smt_commands.append(f"(assert ({expr_map[start]} 0 len))")
    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning(MODULE_CODE, "Nonlinear arithmetic detected, setting logic to QF_AUFNIA")
        smt_commands[1] = "(set-logic QF_AUFNIA)"

    smt = "\n".join(smt_commands)

    return smt


def to_auflia_smtlib2(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the AUFLIA logic."""
    log.debug(MODULE_CODE, 1, f"Encoding MLTL formula in AUFLIA logic:\n\t{repr(start)}")

    is_nonlinear: bool = False 
    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic AUFLIA)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        if typ == types.BoolType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array Int Bool))"
            )
        elif typ == types.IntType():
            smt_commands.append(
                f"(declare-fun f_{signal} () (Array Int Int))"
            )

    for expr in cpt.postorder(start, context):
        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        if expr.type == types.BoolType():
            smt_type = "Bool"
        elif expr.type == types.IntType():
            smt_type = "Int"
        else:
            log.error(MODULE_CODE, f"Unsupported type {expr.type} ({expr})")
            return ""

        fun_signature = f"define-fun {expr_id} ((k Int) (len Int)) {smt_type}"

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            smt_commands.append(f"({fun_signature} true)")
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            smt_commands.append(f"({fun_signature} false)")
        elif isinstance(expr, cpt.Constant):
            smt_commands.append(f"({fun_signature} {expr.value})")
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(
                f"({fun_signature} (select {atomic_map[expr.symbol]} k))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            smt_commands.append(
                f"({fun_signature} (+ ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (* ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (div ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (mod ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (>= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (< ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (<= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (> len k) {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and (> len k) (or {operands})))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len k)  (or (<= len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len)) ({expr_map[expr.children[0]]} i len))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len) ({expr_map[expr.children[1]]} i len) (forall ((j Int)) (=> (and (<= (+ {lb} k) j) (< j i)) ({expr_map[expr.children[0]]} j len)))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                MODULE_CODE, f"Release not implemented for MLTL-SAT via AUFLIA\n\t{expr}"
            )
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append("(declare-fun len () Int)")
    smt_commands.append(f"(assert ({expr_map[start]} 0 len))")
    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning(MODULE_CODE, "Nonlinear arithmetic detected, setting logic to AUFNIA")
        smt_commands[1] = "(set-logic AUFNIA)"

    smt = "\n".join(smt_commands)

    return smt


def to_uflia_smtlib2(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem.

    See https://link.springer.com/chapter/10.1007/978-3-030-25543-5_1

    The paper's implementation is actually incorrect because of the way that duals are defined, especially with regard to the end-of-trace semantics. In the semantics for `p U[lb,ub] q`, where we evaluate `pi` at time `i`, both:

        1) `pi` must be as least as long so as to have data at index `lower_bound + i` (`|pi| > i+lb`) and

        2) there is some `j` where `i+lb <= j <= i+ub` such that `pi` models `q` at `j` and for all `k` where `i+lb <= k < j` we have that `pi` models `p` at `k`.

    Assuming that `(p U[lb,ub] q) = !(!p R[lb,ub] !q)`, then, the semantics of `p R[lb,ub] q` must be such that EITHER 1 fails to hold or the negation of 2 holds. For example, `!(p U[lb,ub] q) = (!p R[lb,ub] !q)` could be true for trace `pi` at time `i` because `|pi| >= i+lb` (this is easier to see when we read the Until expression as "it's NOT the case that `p U[lb,ub] q` holds"). The implementation does not handle the case with `pi` not being long enough correctly. This is only a problem because the operators are defined as duals.

    The same goes for future and global -- `F[l,u] p = ! G[l,u] !p`, where the expression `G[l,u] !p` could be true because `!p` held from `l` to `u` starting at `i`, or because the trace had a length shorter than or equal to `i+l`.

    mltlsat translates all `! G[lb,ub] p` to `True U[lb,ub] !p` and `! F[lb,ub] p` to `False R[lb,ub] !p`

    For atomics, the mltlsat implementation assumes only boolean atomic propositions, which is not a limitation of the approach. Instead of having an uninterpreted function for each atomic, we have an uninterpreted function for each input signal. For example, if `i0` is an `int`, it will have an uninterpreted function `f_i0` that takes an `Int` and returns an `Int`.
    """
    log.debug(MODULE_CODE, 1, f"Encoding MLTL formula in UFLIA logic:\n\t{repr(start)}")

    is_nonlinear: bool = False 
    smt_commands: list[str] = [PREAMBLE]

    smt_commands.append("(set-logic UFLIA)")

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        smt_commands.append(f"(declare-fun f_{signal} (Int) {types.to_smt_type(typ)})")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    for expr in cpt.postorder(start, context):
        if expr.type != types.BoolType() and expr.type != types.IntType():
            log.error(MODULE_CODE, f"Unsupported type {expr.type} ({expr})")
            return ""

        if expr in expr_map:
            continue

        if isinstance(expr, cpt.Atomic):
            expr_map[expr] = expr_map[expr.children[0]]
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        fun_signature = (
            f"define-fun {expr_id} ((k Int) (len Int)) {types.to_smt_type(expr.type)}"
        )

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and expr.value:
            smt_commands.append(f"({fun_signature} true)")
        elif isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type) and not expr.value:
            smt_commands.append(f"({fun_signature} false)")
        elif isinstance(expr, cpt.Constant):
            smt_commands.append(f"({fun_signature} {expr.value})")
        elif isinstance(expr, cpt.Signal) and types.is_bool_type(expr.type):
            smt_commands.append(
                f"({fun_signature} (and (> len k) ({atomic_map[expr.symbol]} k)))"
            )
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(f"({fun_signature} ({atomic_map[expr.symbol]} k))")
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_ADD):
            smt_commands.append(
                f"({fun_signature} (+ ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_SUBTRACT):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MULTIPLY):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (* ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (div ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
            is_nonlinear = True
            smt_commands.append(
                f"({fun_signature} (mod ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_NEGATE):
            smt_commands.append(
                f"({fun_signature} (- ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.NOT_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GREATER_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (>= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (< ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (<= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (> len k) (and {operands})))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and (> len k) (or {operands})))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len k) (or (<= len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len)) ({expr_map[expr.children[0]]} i len))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len) ({expr_map[expr.children[1]]} i len) (forall ((j Int)) (=> (and (<= (+ {lb} k) j) (< j i)) ({expr_map[expr.children[0]]} j len)))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(MODULE_CODE, f"Release not implemented for MLTL-SAT via UFLIA\n\t{expr}")
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr} {type(expr)})")
            return ""

    smt_commands.append("(declare-fun len () Int)")
    smt_commands.append(f"(assert ({expr_map[start]} 0 len))")
    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning(MODULE_CODE, "Nonlinear arithmetic detected, setting logic to UFNIA")
        smt_commands[1] = "(set-logic UFNIA)"

    smt = "\n".join(smt_commands)

    return smt


def check_sat_expr(expr: cpt.Expression, context: cpt.Context) -> SatResult:
    """Returns result of running SMT solver on the SMT encoding of `expr`."""
    log.debug(MODULE_CODE, 1, f"Checking satisfiability:\n\t{repr(expr)}")

    if options.smt_encoding == options.SMTTheories.UFLIA:
        smt = to_uflia_smtlib2(expr, context)
    elif options.smt_encoding == options.SMTTheories.AUFLIA:
        smt = to_auflia_smtlib2(expr, context)
    elif options.smt_encoding == options.SMTTheories.QF_AUFLIA:
        smt = to_qfauflia_smtlib2(expr, context)
    elif options.smt_encoding == options.SMTTheories.AUFBV:
        smt = to_aufbv_smtlib2(expr, context)
    elif options.smt_encoding == options.SMTTheories.QF_AUFBV:
        smt = to_qfaufbv_smtlib2(expr, context)
    elif options.smt_encoding == options.SMTTheories.QF_BV:
        smt = to_qfbv_smtlib2(expr, context, expr.wpd + 1)
    elif options.smt_encoding == options.SMTTheories.QF_BV_INCR:
        return check_sat_qfbv_incr(expr, context)
    else:
        log.error(MODULE_CODE, f"Unsupported SMT theory {options.smt_encoding}")
        return SatResult.UNKNOWN
    
    log.debug(MODULE_CODE, 2, f"SMT encoding:\n{smt}")

    (result, time) = run_smt_solver(smt, options.timeout_sat)
    log.stat(MODULE_CODE, f"sat_result={result.value}")
    log.stat(MODULE_CODE, f"sat_time={time}")
    log.stat(MODULE_CODE, "num_sat_calls=1")
    return result


def check_sat(
    program: cpt.Program, context: cpt.Context
) -> "dict[cpt.Specification, SatResult]":
    """Runs an SMT solver on the SMT encoding of the MLTL formulas in `program`."""
    if not check_solver():
        log.error(MODULE_CODE, f"{options.smt_solver} not found")
        return {}

    results: dict[cpt.Specification, SatResult] = {}

    for spec in program.ft_spec_set.get_specs():
        if isinstance(spec, cpt.Contract):
            log.warning(MODULE_CODE, "Found contract, skipping")
            continue

        expr = spec.get_expr()
        results[spec] = check_sat_expr(expr, context)

    return results


def check_equiv(
    expr1: cpt.Expression, expr2: cpt.Expression, context: cpt.Context
) -> SatResult:
    """Returns true if `expr1` is equivalent to `expr2`, false if they are not, and None if the check timed our or failed in some other way.

    To check equivalence, this function encodes the formula `!(expr1 <-> expr2)`: if this formula is unsatisfiable it means there is no trace `pi` such that `pi |== expr` and `pi |=/= expr` or vice versa.
    """
    log.debug(
        MODULE_CODE,
        1,
        f"Checking equivalence:\n\t{repr(expr1)}\n\t\t<->\n\t{repr(expr2)}",
    )

    neg_equiv_expr = cpt.Operator.LogicalNegate(
        expr1.loc, cpt.Operator.LogicalIff(expr1.loc, expr1, expr2)
    )

    start = util.get_rusage_time()

    result = check_sat_expr(neg_equiv_expr, context)

    end = util.get_rusage_time()
    equiv_time = end - start
    if equiv_time > float(options.timeout_sat):
        log.stat(MODULE_CODE, "equiv_check_time=timeout")
    else:
        log.stat(MODULE_CODE, f"equiv_check_time={equiv_time}")

    if result is SatResult.SAT:
        log.debug(MODULE_CODE, 1, "Not equivalent")
    elif result is SatResult.UNSAT:
        log.debug(MODULE_CODE, 1, "Equivalent")
    else:
        log.debug(MODULE_CODE, 1, "Unknown")

    return result
