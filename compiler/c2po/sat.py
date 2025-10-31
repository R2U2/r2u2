import subprocess
import enum
import sys
import math

from typing import cast

from c2po import cpt, log, util, types, options

MODULE_CODE = "SAT"

PREAMBLE = f"""(set-info :source |SMT encoding for satisfiability checking of Mission-time Linear Temporal Logic (MLTL) formulas.\nEncoded by C2PO v{log.VERSION}, see https://github.com/R2U2/r2u2/tree/develop/compiler.|)"""


class SatResult(enum.Enum):
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"
    TIMEOUT = "timeout"
    MEMOUT = "memout"
    FAILURE = "fail"


def check_solver(smt_solver: str) -> bool:
    try:
        proc0 = subprocess.run([smt_solver, "-version"], capture_output=True)
        proc1 = subprocess.run([smt_solver, "--version"], capture_output=True)
        return proc0.returncode == 0 or proc1.returncode == 0
    except FileNotFoundError:
        return False


def run_smt_solver(smt_encoding: str, timeout: float, context: cpt.Context) -> tuple[SatResult, float]:
    """Runs the SMT solver on the given SMT-LIB2 encoding and returns the result."""
    log.debug(MODULE_CODE, 1, "Running SMT solver.")

    if not check_solver(context.options.smt_solver_path):
        log.error(MODULE_CODE, f"{context.options.smt_solver_path} not found")
        return (SatResult.FAILURE, -1.0)

    smt_file_path = context.options.workdir / "__tmp__.smt"
    with open(smt_file_path, "w") as f:
        f.write(smt_encoding)

    command = [context.options.smt_solver_path, str(smt_file_path)] + [opt.replace('"', '') for opt in context.options.smt_options]
    if (
        context.options.smt_encoding == options.SMTTheories.UFLIA
        or context.options.smt_encoding == options.SMTTheories.QF_UFLIA
    ) and "cvc5" in context.options.smt_solver_path:
        # cvc5 requires the --finite-model-find option for UFLIA encoding
        command.append("--finite-model-find")
        command.append("--fmf-bound")

    log.debug(MODULE_CODE, 1, f"Running '{' '.join(command)}'")

    start = util.get_rusage_time()
    proc = subprocess.Popen(command, preexec_fn=util.set_max_memory_offset(context.options.smt_max_memory), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    try:
        (stdout, stderr) = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        log.warning(MODULE_CODE, f"{context.options.smt_solver_path} timed out")
        return (SatResult.TIMEOUT, -1.0)
    
    end = util.get_rusage_time()
    stdout = stdout.decode() if stdout else ""
    stderr = stderr.decode() if stderr else ""

    if proc.returncode != 0:
        # z3 memout: 
        #   stdout=
        #   stderr=(error "out of memory")
        #   returncode=101
        if "z3" in context.options.smt_solver_path and "(error \"out of memory\")" in stderr:
            log.warning(MODULE_CODE, f"{context.options.smt_solver_path} ran out of memory")
            return (SatResult.MEMOUT, -1.0)

        # cvc5 memout: 
        #   stdout(error "std::bad_alloc")
        #   stderr=
        #   returncode=1
        if "cvc5" in context.options.smt_solver_path and "std::bad_alloc" in stdout or "std::bad_alloc" in stderr:
            log.warning(MODULE_CODE, f"{context.options.smt_solver_path} ran out of memory")
            return (SatResult.MEMOUT, -1.0)

        # yices memout:
        #   stdout=
        #   stderr=out of memory
        #   returncode=16
        if "yices" in context.options.smt_solver_path and "Out of memory" in stderr:
            log.warning(MODULE_CODE, f"{context.options.smt_solver_path} ran out of memory")
            return (SatResult.MEMOUT, -1.0)

        # mathsat memout
        #   stdout=
        #   stderr=
        #   returncode=6
        if "mathsat" in context.options.smt_solver_path and proc.returncode == -6:
            log.warning(MODULE_CODE, f"{context.options.smt_solver_path} ran out of memory")
            return (SatResult.MEMOUT, -1.0)

        # bitwuzla memout
        #   stdout=
        #   stderr=terminate called after throwing an instance of 'std::bad_alloc'
        #            what():  std::bad_alloc
        #   returncode=-6
        if "bitwuzla" in context.options.smt_solver_path and "std::bad_alloc" in stderr:
            log.warning(MODULE_CODE, f"{context.options.smt_solver_path} ran out of memory")
            return (SatResult.MEMOUT, -1.0)
        
        log.error(
            MODULE_CODE,
            f"{context.options.smt_solver_path} failed with return code {proc.returncode}",
        )
        log.debug(MODULE_CODE, 1, "stdout:")
        print(stdout[:-1])
        log.debug(MODULE_CODE, 1, "stderr:")
        print(stderr[:-1])
        return (SatResult.FAILURE, -1.0)

    if stdout.find("unsat") > -1:
        log.debug(MODULE_CODE, 1, "unsat")
        result = SatResult.UNSAT
    elif stdout.find("sat") > -1:
        log.debug(MODULE_CODE, 1, "sat")
        result = SatResult.SAT
    else:
        log.debug(MODULE_CODE, 1, "unknown")
        result = SatResult.UNKNOWN

    sat_time = end - start
    return (result, sat_time)


def to_qfbv_smtlib2(start: cpt.Expression, context: cpt.Context, trace_len: int) -> str:
    log.debug(
        MODULE_CODE,
        1,
        f"Encoding MLTL formula in QF_BV logic (up to length {trace_len}):\n\t{repr(start)}",
    )

    bv_width = trace_len
    bv_sort = f"(_ BitVec {bv_width})"

    # Need to set this in case bv literals have more than 4300 digits (in decimal) for to_bv
    # 0 means no limit
    sys.set_int_max_str_digits(0) 

    def to_bv(value: int):
        nonlocal bv_width
        return f"(_ bv{min(value, (2**bv_width) - 1)} {bv_width})"

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

    decomposed_expr = cpt.decompose_intervals(start, context)
    for expr in cpt.postorder(decomposed_expr, context):
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

        fun_signature = "define-fun {0} () " + bv_sort

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature.format(expr_id)} {ones()})")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature.format(expr_id)} {zeros()})")
        elif isinstance(expr, cpt.Signal):
            smt_commands.append(f"({fun_signature.format(expr_id)} {atomic_map[expr.symbol]})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature.format(expr_id)} (bvnot {expr_map[expr.children[0]]}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            op = f"(bvand {expr_map[expr.children[0]]} {expr_map[expr.children[1]]})"
            for child in expr.children[2:]:
                op = f"(bvand {op} {expr_map[child]})"
            smt_commands.append(f"({fun_signature.format(expr_id)} {op})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            op = f"(bvor {expr_map[expr.children[0]]} {expr_map[expr.children[1]]})"
            for child in expr.children[2:]:
                op = f"(bvor {op} {expr_map[child]})"
            smt_commands.append(f"({fun_signature.format(expr_id)} {op})")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(
                f"({fun_signature.format(expr_id)} (bvxnor {expr_map[expr.children[0]]} {expr_map[expr.children[1]]}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            child = expr.children[0]
            lb = expr.interval.lb
            ub = expr.interval.ub
            i = 0

            if ub == 0:
                # then expr is G[0,0] phi
                smt_commands.append(
                    f"({fun_signature.format(expr_id)} {expr_map[child]})"
                )
                continue
            elif lb > 0:
                # then expr is G[a,a+2^k-1] phi
                shift_amt = lb
                shift_ones_bitmask = to_bv(2**shift_amt - 1)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvor (bvshl {expr_map[expr.children[0]]} {to_bv(shift_amt)}) {shift_ones_bitmask}))"
                )
                i += 1
                ub -= lb

            for j in range(0, int(math.log2(ub+1))):
                shift_amt = 2**j
                shift_ones_bitmask = to_bv(2**shift_amt - 1)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvor (bvshl {f'{expr_id}_{i-1}' if i > 0 else expr_map[expr.children[0]]} {to_bv(shift_amt)}) {shift_ones_bitmask}))"
                )
                i += 1
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvand {f'{expr_id}_{i-1}'} {f'{expr_id}_{i-2}' if i > 1 else expr_map[expr.children[0]]}))"
                )
                i += 1

            smt_commands.append(
                f"({fun_signature.format(expr_id)} {f'{expr_id}_{i-1}'})"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            child = expr.children[0]
            lb = expr.interval.lb
            ub = expr.interval.ub
            i = 0

            if ub == 0:
                smt_commands.append(
                    f"({fun_signature.format(expr_id)} {expr_map[child]})"
                )
                continue
            elif lb > 0:
                shift_amt = lb
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvshl {expr_map[expr.children[0]]} {to_bv(shift_amt)}))"
                )
                i += 1
                ub -= lb

            for j in range(0, int(math.log2(ub+1))):
                shift_amt = 2**j
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvshl {f'{expr_id}_{i-1}' if i > 0 else expr_map[expr.children[0]]} {to_bv(shift_amt)}))"
                )
                i += 1
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_{i}')} (bvor {f'{expr_id}_{i-1}'} {f'{expr_id}_{i-2}' if i > 1 else expr_map[expr.children[0]]}))"
                )
                i += 1

            smt_commands.append(
                f"({fun_signature.format(expr_id)} {f'{expr_id}_{i-1}'})"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lhs = expr.children[0]
            rhs = expr.children[1]
            lb = expr.interval.lb
            ub = expr.interval.ub
            i = 0
            j = 0

            if ub == 0:
                smt_commands.append(
                    f"({fun_signature.format(expr_id)} {expr_map[rhs]})"
                )
                continue
            elif lb > 0:
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_L_{j}')} (bvshl {expr_map[lhs]} {to_bv(lb)}))"
                )
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i}')} (bvshl {expr_map[rhs]} {to_bv(lb)}))"
                )
                i += 1
                j += 1
                ub -= lb
             
            for k in range(0, int(math.log2(ub+1))):
                # expr_R = expr_R_{j} | (expr_L_{i-1} & (expr_R_{j} << 2^k))
                # (expr_R_{i} << 1)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i}')} (bvshl {f'{expr_id}_R_{i-1}' if i > 0 else expr_map[rhs]} {to_bv(2**k)}))"
                )
                # (expr_L_{j-1} & (expr_R_{i} << 2^k))
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i+1}')} (bvand {f'{expr_id}_R_{i}'} {f'{expr_id}_L_{j-1}' if j > 0 else expr_map[lhs]}))"
                )
                # expr_R_{i} | (expr_L_{j-1} & (expr_R_{i} << 2^k))
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_R_{i+2}')} (bvor {f'{expr_id}_R_{i+1}'} {f'{expr_id}_R_{i-1}' if i > 0 else expr_map[rhs]}))"
                )
                i += 3

                # expr_L = expr_L_{j-1} & (expr_L_{j-1} << 2^k)
                # expr_L_{j-1} << 2^k
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_L_{j}')} (bvshl {f'{expr_id}_L_{j-1}' if j > 0 else expr_map[lhs]} {to_bv(2**k)}))"
                )
                # expr_R_{j-1} & (expr_R_{j-1} << 2^k)
                smt_commands.append(
                    f"({fun_signature.format(f'{expr_id}_L_{j+1}')} (bvand {f'{expr_id}_L_{j}'} {f'{expr_id}_L_{j-1}' if j > 0 else expr_map[lhs]}))"
                )
                j += 2

            smt_commands.append(
                f"({fun_signature.format(expr_id)} {f'{expr_id}_R_{i-1}'})"
            )
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append(f"(assert (bvugt {expr_map[decomposed_expr]} {zeros()}))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def to_qfuflia_smtlib2(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the QF_UFLIA logic."""
    log.debug(
        MODULE_CODE, 1, f"Encoding MLTL formula in QF_UFLIA logic:\n\t{repr(start)}"
    )

    is_nonlinear: bool = False
    smt_commands: list[str] = [PREAMBLE]
    smt_commands.append("(set-logic QF_UFLIA)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[str, str] = {}
    for signal, typ in context.signals.items():
        atomic_map[signal] = f"f_{signal}"
        smt_commands.append(f"(declare-fun f_{signal} (Int) {types.to_smt_type(typ)})")

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
                f"(=> (> len (+ k {i})) ({expr_map[expr.children[0]]} (+ k {i}) len))"
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
                unroll = f"(or ({expr_map[expr.children[1]]} (+ {i} k) len) (and ({expr_map[expr.children[0]]} (+ {i} k) len) {unroll}))"

            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) {unroll}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                MODULE_CODE, f"Release not implemented for MLTL-SAT via QF_UFLIA\n\t{expr}"
            )
            return ""
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr})")
            return ""

    smt_commands.append("(declare-fun len () Int)")
    smt_commands.append(f"(assert ({expr_map[start]} 0 len))")
    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning(MODULE_CODE, "Nonlinear arithmetic detected, setting logic to QF_UFNIA")
        smt_commands[1] = "(set-logic QF_UFNIA)"

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
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len k) (or (<= len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) (< i len)) (or ({expr_map[expr.children[1]]} i len) (exists ((j Int)) (and (<= (+ {lb} k) j) (< j i) ({expr_map[expr.children[0]]} j len)))))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.ONCE):
            # pi,k |= O[lb,ub] p iff lb < k < |pi| and there exists i such that k-ub <= i <= k-lb
            # and pi,i |= p
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (and (< {lb} k) (< k len)) (exists ((i Int)) (and (<= (- k {ub}) i) (<= i (- k {lb})) (> i 0) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.HISTORICAL):
            # pi,k |= H[lb,ub] p iff ! (lb < k < |pi|) or for all i such that k-ub <= i <= k-lb it
            # holds that pi,i |= p
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (not (and (< {lb} k) (< k len))) (forall ((i Int)) (=> (<= (- k {ub}) i) (<= i (- k {lb})) (> i 0) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.SINCE):
            # pi,k |= p S[lb,ub] q iff lb < k < |pi| and there exists i such that k-ub <= i <= k-lb
            # and pi,i |= p and for all j such that i < j <= k it holds that pi,j |= q
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (not (and (< {lb} k) (< k len))) (forall ((i Int)) (=> (<= (- k {ub}) i) (<= i (- k {lb})) (> i 0) ({expr_map[expr.children[0]]} i len)))))"
            )
        else:
            log.error(MODULE_CODE, f"Unsupported operator ({expr} {type(expr)})")
            return ""

    smt_commands.append(f"(assert (exists ((len Int)) ({expr_map[start]} 0 len)))")
    smt_commands.append("(check-sat)")

    if is_nonlinear:
        log.warning(MODULE_CODE, "Nonlinear arithmetic detected, setting logic to UFNIA")
        smt_commands[1] = "(set-logic UFNIA)"

    smt = "\n".join(smt_commands)

    return smt


def check_sat_qfbv_incr(start: cpt.Expression, context: cpt.Context) -> SatResult:
    """Incrementally searches for an int `len` up to `start.wpd` such that `check_sat(to_qfbv_smtlib2(start, context, len))` is not unknown."""
    total_sat_time: float = 0
    total_enc_time: float = 0
    trace_len: int = 1

    def update_stats(enc_time: float, sat_time: float, result: SatResult) -> None:
        context.stats.smt_num_calls += 1
        context.stats.smt_solver_time += sat_time
        context.stats.smt_encoding_time += enc_time
        context.stats.smt_solver_result = result.value

    def done(result: SatResult) -> bool:
        # We know we are done when the result is sat, timeout, or failure or we have checked traces with length up to start.wpd + 1
        nonlocal trace_len
        return result in {SatResult.SAT, SatResult.TIMEOUT, SatResult.MEMOUT, SatResult.FAILURE} or trace_len >= (start.wpd + 1)

    log.debug(
        MODULE_CODE,
        1,
        f"Checking satisfiability of MLTL formula in QF_BV logic:\n\t{repr(start)}",
    )

    if context.options.enable_booleanizer:
        log.warning(
            MODULE_CODE,
            "Booleanizer enabled, skipping QF_BV sat check.\n\t"
            "Consider using a different SMT theory.",
        )
        return SatResult.UNKNOWN

    # start with a quick check
    enc_start = util.get_rusage_time()
    smt = to_qfbv_smtlib2(start, context, trace_len)
    enc_end = util.get_rusage_time()
    enc_time = enc_end - enc_start
    total_enc_time += enc_time

    (result, sat_time) = run_smt_solver(smt, context.options.smt_max_time, context)

    total_sat_time += sat_time
    update_stats(enc_time, sat_time, result)
    if done(result):
        return result

    # if wpd is less than 256 then just go straight for it
    if start.wpd <= 255:
        trace_len = start.wpd + 1
        enc_start = util.get_rusage_time()
        smt = to_qfbv_smtlib2(start, context, trace_len)
        enc_end = util.get_rusage_time()
        enc_time = enc_end - enc_start
        total_enc_time += enc_time

        (result, sat_time) = run_smt_solver(smt, context.options.smt_max_time - total_sat_time, context)

        total_sat_time += sat_time
        update_stats(enc_time, sat_time, result)
        return result

    # otherwise wpd >= 256, so try its bpd first, then its wpd
    trace_len = start.bpd + 1
    enc_start = util.get_rusage_time()
    smt = to_qfbv_smtlib2(start, context, trace_len)
    enc_end = util.get_rusage_time()
    enc_time = enc_end - enc_start
    total_enc_time += enc_time

    (result, sat_time) = run_smt_solver(smt, context.options.smt_max_time - total_sat_time, context)

    total_sat_time += sat_time
    update_stats(enc_time, sat_time, result)
    if done(result):
        return result
    
    trace_len = start.wpd + 1
    enc_start = util.get_rusage_time()
    smt = to_qfbv_smtlib2(start, context, trace_len)
    enc_end = util.get_rusage_time()
    enc_time += enc_end - enc_start
    total_enc_time += enc_time

    (result, sat_time) = run_smt_solver(smt, context.options.smt_max_time - total_sat_time, context)

    total_sat_time += sat_time
    update_stats(enc_time, sat_time, result)
    return result


def check_sat_expr(expr: cpt.Expression, context: cpt.Context) -> SatResult:
    """Returns result of running SMT solver on the SMT encoding of `expr`."""
    log.debug(MODULE_CODE, 1, f"Checking satisfiability:\n\t{repr(expr)}")

    if not check_solver(context.options.smt_solver_path):
        log.error(MODULE_CODE, f"{context.options.smt_solver_path} not found")
        return SatResult.FAILURE

    start = util.get_rusage_time()
    if context.options.smt_encoding == options.SMTTheories.UFLIA:
        smt = to_uflia_smtlib2(expr, context)
    elif context.options.smt_encoding == options.SMTTheories.QF_UFLIA:
        smt = to_qfuflia_smtlib2(expr, context)
    elif context.options.smt_encoding == options.SMTTheories.QF_BV:
        smt = to_qfbv_smtlib2(expr, context, expr.wpd + 1)
    elif context.options.smt_encoding == options.SMTTheories.QF_BV_INCR:
        return check_sat_qfbv_incr(expr, context)
    else:
        log.error(MODULE_CODE, f"Unsupported SMT theory {context.options.smt_encoding}")
        return SatResult.UNKNOWN
    end = util.get_rusage_time()
    encoding_time = end - start

    (result, solving_time) = run_smt_solver(smt, context.options.smt_max_time, context)

    context.stats.smt_encoding_time += encoding_time
    context.stats.smt_solver_time += solving_time
    context.stats.smt_num_calls += 1
    context.stats.smt_solver_result = result.value

    return result


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

    result = check_sat_expr(neg_equiv_expr, context)

    context.stats.eqsat_equiv_encoding_time = context.stats.smt_encoding_time
    context.stats.eqsat_equiv_solver_time = context.stats.smt_solver_time
    context.stats.eqsat_equiv_result = result.value
    context.stats.reset_smt_stats()

    if result is SatResult.SAT:
        log.debug(MODULE_CODE, 1, "Not equivalent")
    elif result is SatResult.UNSAT:
        log.debug(MODULE_CODE, 1, "Equivalent")
    else:
        log.debug(MODULE_CODE, 1, "Unknown")

    return result
