import subprocess
import enum

from typing import cast

from c2po import cpt, log, util, types, options

MODULE_CODE = "SAT"


class SatResult(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


def check_solver() -> bool:
    try:
        proc0 = subprocess.run([options.smt_solver, "-version"], capture_output=True)
        proc1 = subprocess.run([options.smt_solver, "--version"], capture_output=True)
        return proc0.returncode == 0 or proc1.returncode == 0
    except FileNotFoundError:
        return False


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

    smt_commands: list[str] = []
    smt_commands.append("(set-logic AUFBV)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal,typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        if typ == types.BoolType():
            smt_commands.append(f"(declare-fun f_{signal} () (Array {timestamp_sort} Bool))")
        elif typ == types.IntType():
            smt_commands.append(f"(declare-fun f_{signal} () (Array {timestamp_sort} (_ BitVec {types.IntType().width})))")

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

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) true))")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) false))")
        elif isinstance(expr, cpt.Signal) and types.is_bool_type(expr.type):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (select {atomic_map[expr.symbol]} k)))"
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
                f"({fun_signature} (and (bvugt len k) ({op} (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            op = "bvult" if not types.IntType().is_signed else "bvslt"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            op = "bvule" if not types.IntType().is_signed else "bvsle"
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) ({op} (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (not ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and {operands}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (or {operands}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (or (bvule len (bvadd {to_bv(lb)} k)) (forall ((i {timestamp_sort})) (=> (and (bvule (bvadd {to_bv(lb)} k) i) (bvule i (bvadd {to_bv(ub)} k)) (bvult i len)) ({expr_map[expr.children[0]]} i len)))))"
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
                MODULE_CODE, f"Release not implemented for MLTL-SAT via QF_BV\n\t{expr}"
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

    smt_commands: list[str] = []

    smt_commands.append("(set-logic UFLIA)")

    atomic_map: dict[str, str] = {}
    for signal,typ in context.signals.items():
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

        fun_signature = f"define-fun {expr_id} ((k Int) (len Int)) {types.to_smt_type(expr.type)}"

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature} true)")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature} false)")
        elif isinstance(expr, cpt.Signal) and types.is_bool_type(expr.type):
            smt_commands.append(
                f"({fun_signature} (and (> len k) ({atomic_map[expr.symbol]} k)))"
            )
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(
                f"({fun_signature} ({atomic_map[expr.symbol]} k))"
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
            smt_commands.append(
                f"({fun_signature} (* ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_DIVIDE):
            smt_commands.append(
                f"({fun_signature} (div ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ARITHMETIC_MODULO):
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
                f"({fun_signature} (and (> len k) (>= (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (< ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LESS_THAN_OR_EQUAL):
            smt_commands.append(
                f"({fun_signature} (and (> len k) (<= (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (not ({expr_map[expr.children[0]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (and {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(f"({fun_signature} (or {operands}))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(
                f"({fun_signature} (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature} (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len)))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (or (<= len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len)) ({expr_map[expr.children[0]]} i len)))))"
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
            log.error(MODULE_CODE, f"Release not implemented for MLTL-SAT\n\t{expr}")
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr} {type(expr)})")
            return ""

    smt_commands.append("(declare-fun len () Int)")
    smt_commands.append(f"(assert ({expr_map[start]} 0 len))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def check_sat_expr(expr: cpt.Expression, context: cpt.Context) -> SatResult:
    """Returns result of running SMT solver on the SMT encoding of `expr`."""
    log.debug(MODULE_CODE, 1, f"Checking satisfiability:\n\t{repr(expr)}")

    if not check_solver():
        log.error(MODULE_CODE, f"{options.smt_solver} not found")
        return SatResult.UNKNOWN

    if options.smt_theory == options.SMTTheories.UFLIA:
        smt = to_uflia_smtlib2(expr, context)
    elif options.smt_theory == options.SMTTheories.AUFBV:
        smt = to_aufbv_smtlib2(expr, context)
    else:
        log.error(MODULE_CODE, f"Unsupported SMT theory {options.smt_theory}")
        return SatResult.UNKNOWN

    smt_file_path = options.workdir / "__tmp__.smt"
    with open(smt_file_path, "w") as f:
        f.write(smt)

    command = [options.smt_solver, str(smt_file_path)]
    if options.smt_options != "":
        command += options.smt_options.split(" ")
    log.debug(MODULE_CODE, 1, f"Running '{' '.join(command)}'")

    try:
        start = util.get_rusage_time()
        proc = subprocess.run(
            command, capture_output=True, timeout=options.timeout_sat
        )
        end = util.get_rusage_time()
    except subprocess.TimeoutExpired:
        log.warning(MODULE_CODE, f"{options.smt_solver} timeout after {options.timeout_sat}s")
        log.stat(MODULE_CODE, "sat_check_time=timeout")
        log.stat(MODULE_CODE, f"sat_result={SatResult.UNKNOWN.value}")
        return SatResult.UNKNOWN
    
    if proc.returncode != 0:
        log.error(MODULE_CODE, f"{options.smt_solver} failed with return code {proc.returncode}")
        log.debug(MODULE_CODE, 1, proc.stdout.decode()[:-1])
        return SatResult.UNKNOWN

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
    log.stat(MODULE_CODE, f"sat_time={sat_time}")
    log.stat(MODULE_CODE, f"sat_result={result.value}")

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
