import subprocess
import enum
import pathlib

from typing import cast

from c2po import cpt, log, util, types

MODULE_CODE = "SAT"

Z3 = "z3"


class SatResult(enum.Enum):
    SAT = 0
    UNSAT = 1
    UNKNOWN = 2


def check_solver_installed(solver: str) -> bool:
    try:
        proc = subprocess.run([solver, "-version"], capture_output=True)
        return proc.returncode == 0
    except FileNotFoundError:
        return False


def to_smt_sat_query_bv(start: cpt.Expression, context: cpt.Context, mission_time: int) -> str:
    """FIXME: Until not implemented correctly

    Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem using the QF_BV logic.

    See https://link.springer.com/chapter/10.1007/978-3-030-25543-5_1
    """
    if mission_time > 0:
        mission_time = mission_time
    else:
        mission_time = start.wpd

    idx_size = mission_time.bit_length()

    trace_sort = f"(_ BitVec {mission_time})"
    idx_sort = f"(_ BitVec {idx_size})"
    # const_one_trace = f"#b{'0'*(mission_time-1)}1"
    # const_zero_trace = f"#b{'0'*(mission_time-1)}1"

    def ones(length: int):
        return f"#b{'1'*length}"

    def zeroes(length: int):
        return f"#b{'0'*length}"

    def one_in_idx(length: int, idx: int):
        return f"#b{'0'*(length-(length-idx))}1{'0'*(length-idx-1)}"

    def to_bv(length: int, value: int):
        return f"(_ bv{value} {length})"

    smt_commands: list[str] = []
    smt_commands.append("(set-logic QF_UFBV)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    atomic_map: dict[cpt.Expression, str] = {}
    for atomic, id in context.atomic_id.items():
        atomic_map[atomic] = f"f_a{id}"
        smt_commands.append(f"(declare-const {atomic_map[atomic]} {trace_sort})")

    for expr in cpt.postorder(start, context):
        if expr in expr_map:
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        fun_signature = f"define-fun {expr_id} ((k {idx_sort}) (len {idx_sort})) Bool"

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) true))")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature} (and (bvugt len k) false))")
        elif expr in context.atomic_id:
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (= ((_ extract 0 0) (bvshl {atomic_map[expr]} ((_ zero_extend {mission_time - idx_size}) k)) #b1) ))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (not ({expr_map[expr.children[0]]} k len))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join(
                [f"({expr_map[child]} k len)" for child in expr.children]
            )
            smt_commands.append(
                f"({fun_signature} (and (bvugt len k) (and {operands})))"
            )
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

            if lb == ub:
                smt_expr = f"({expr_map[expr.children[0]]} {lb} len)"
            else:
                smt_expr = f"(and {' '.join([f'({expr_map[expr.children[0]]} {i} len)' for i in range(lb,ub+1)])})"

            smt_commands.append(
                f"({fun_signature} (and (bvugt len (bvadd {to_bv(idx_size, lb)} k)) {smt_expr}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub

            if lb == ub:
                smt_expr = f"({expr_map[expr.children[0]]} {lb} len)"
            else:
                smt_expr = f"(or {' '.join([f'({expr_map[expr.children[0]]} {i} len)' for i in range(lb,ub+1)])})"

            smt_commands.append(
                f"({fun_signature} (and (bvugt len (bvadd {to_bv(idx_size, lb)} k)) {smt_expr}))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            log.error(
                MODULE_CODE, f"Until not implemented for MLTL-SAT via QF_BV\n\t{expr}"
            )
            return ""

            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub

            if lb == ub:
                smt_expr = f"({expr_map[expr.children[1]]} {lb} len)"
            else:
                cases = " ".join(
                    [
                        f"(and ({expr_map[expr.children[0]]} {i} len))"
                        for i in range(lb, ub + 1)
                    ]
                )
                smt_expr = f"(or {cases})"

            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) ({expr_map[expr.children[1]]} i (- len i)) (forall ((j Int)) (=> (and (<= (+ {lb} k) j) (< j i)) ({expr_map[expr.children[0]]} j len)))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(
                MODULE_CODE, f"Release not implemented for MLTL-SAT via QF_BV\n\t{expr}"
            )
            return ""
        else:
            log.error(MODULE_CODE, f"Bad repr ({expr})")
            return ""

    smt_commands.append(f"(assert ({expr_map[start]} 0 {mission_time}))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def to_uflia_sat_query(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem.

    See https://link.springer.com/chapter/10.1007/978-3-030-25543-5_1

    The paper's implementation is actually incorrect because of the way that duals are defined, especially with regard to the end-of-trace semantics. In the semantics for `p U[lb,ub] q`, where we evaluate `pi` at time `i`, both:

        1) `pi` must be as least as long so as to have data at index `lower_bound + i` (`|pi| > i+lb`) and

        2) there is some `j` where `i+lb <= j <= i+ub` such that `pi` models `q` at `j` and for all `k` where `i+lb <= k < j` we have that `pi` models `p` at `k`.

    Assuming that `(p U[lb,ub] q) = !(!p R[lb,ub] !q)`, then, the semantics of `p R[lb,ub] q` must be such that EITHER 1 fails to hold or the negation of 2 holds. For example, `!(p U[lb,ub] q) = (!p R[lb,ub] !q)` could be true for trace `pi` at time `i` because `|pi| >= i+lb` (this is easier to see when we read the Until expression as "it's NOT the case that `p U[lb,ub] q` holds"). The implementation does not handle the case with `pi` not being long enough correctly. This is only a problem because the operators are defined as duals.

    The same goes for future and global -- `F[l,u] p = ! G[l,u] !p`, where the expression `G[l,u] !p` could be true because `!p` held from `l` to `u` starting at `i`, or because the trace had a length shorter than or equal to `i+l`.

    mltlsat translates all `! G[lb,ub] p` to `True U[lb,ub] !p` and `! F[lb,ub] p` to `False R[lb,ub] !p`
    """
    smt_commands: list[str] = []

    smt_commands.append("(set-logic AUFLIA)")

    atomic_map: dict[cpt.Expression, str] = {}
    for atomic, id in context.atomic_id.items():
        atomic_map[atomic] = f"f_a{id}"
        smt_commands.append(f"(declare-fun {atomic_map[atomic]} (Int) Bool)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    for expr in cpt.postorder(start, context):
        if expr in expr_map or (
            expr.engine is not types.R2U2Engine.TEMPORAL_LOGIC
            and expr not in context.atomic_id
            and not isinstance(expr, cpt.Constant)
        ):
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        fun_signature = f"define-fun {expr_id} ((k Int) (len Int)) Bool"

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature} true)")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature} false)")
        elif expr in context.atomic_id:
            smt_commands.append(
                f"({fun_signature} (and (> len k) ({atomic_map[expr]} k)))"
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
            log.error(MODULE_CODE, f"Bad repr ({expr})")
            return ""

    smt_commands.append(f"(assert (exists ((len Int)) ({expr_map[start]} 0 len)))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def check_sat_expr(expr: cpt.Expression, context: cpt.Context, workdir: pathlib.Path, timeout: int) -> SatResult:
    """Returns result of running SMT solver on the SMT encoding of `expr`."""
    log.debug(MODULE_CODE, 1, f"Checking satisfiability:\n\t{repr(expr)}")

    if not check_solver_installed(Z3):
        log.error(MODULE_CODE, "z3 not found")
        return SatResult.UNKNOWN

    smt = to_uflia_sat_query(expr, context)

    smt_file_path = workdir / "__tmp__.smt"
    with open(smt_file_path, "w") as f:
        f.write(smt)

    command = [Z3, str(smt_file_path)]
    log.debug(MODULE_CODE, 1, f"Running '{' '.join(command)}'")

    start = util.get_rusage_time()

    try:
        proc = subprocess.run(
            command, capture_output=True, timeout=timeout
        )
    except subprocess.TimeoutExpired:
        log.warning(MODULE_CODE, f"z3 timeout after {timeout}s")
        log.stat(MODULE_CODE, "sat_check_time=timeout")
        return SatResult.UNKNOWN

    end = util.get_rusage_time()
    sat_time = end - start
    log.stat(MODULE_CODE, f"sat_check_time={sat_time}")

    smt_file_path.unlink()

    if proc.stdout.decode().find("unsat") > -1:
        log.debug(MODULE_CODE, 1, "unsat")
        return SatResult.UNSAT
    elif proc.stdout.decode().find("sat") > -1:
        log.debug(MODULE_CODE, 1, "sat")
        return SatResult.SAT
    else:
        log.debug(MODULE_CODE, 1, "unknown")
        return SatResult.UNKNOWN


def check_sat(
    program: cpt.Program, context: cpt.Context, workdir: pathlib.Path, timeout: int
) -> "dict[cpt.Specification, SatResult]":
    """Runs an SMT solver (Z3 by default) on the SMT encoding of the MLTL formulas in `program`."""
    if not check_solver_installed(Z3):
        log.error(MODULE_CODE, "z3 not found")
        return {}

    results: dict[cpt.Specification, SatResult] = {}

    for spec in program.ft_spec_set.get_specs():
        if isinstance(spec, cpt.Contract):
            log.warning(MODULE_CODE, "Found contract, skipping")
            continue

        expr = spec.get_expr()
        results[spec] = check_sat_expr(expr, context, workdir, timeout)

    return results


def check_equiv(
    expr1: cpt.Expression, expr2: cpt.Expression, context: cpt.Context, workdir: pathlib.Path, timeout: int
) -> SatResult:
    """Returns true if `expr1` is equivalent to `expr2`, false if they are not, and None if the check timed our or failed in some other way.

    To check equivalence, this function encodes the formula `!(expr1 <-> expr2)`: if this formula is unsatisfiable it means there is no trace `pi` such that `pi |= expr` and `pi |/= expr` or vice versa.
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

    result = check_sat_expr(neg_equiv_expr, context, workdir, timeout)

    end = util.get_rusage_time()
    equiv_time = end - start
    if equiv_time > float(timeout):
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
