import pathlib
import shutil
import subprocess
import enum

from typing import cast, Optional

from c2po import cpt, log

MODULE_CODE = "SAT"

WORK_DIR = pathlib.Path(__file__).parent / "__workdir__"

Z3 = "z3"

class SatResult(enum.Enum):
    SAT = 0
    UNSAT = 1
    UNKNOWN = 2


def check_solver_installed(solver: str) -> bool:
    proc = subprocess.run([solver, "-version"], capture_output=True)
    return proc.returncode == 0


def to_smt_sat_query_rec(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a single-formula string representing an SMT-LIB2 encoding of the MLTL sat problem. This is more faithful than `to_smt_sat_query` to the encoding found in the artifact repo: https://github.com/cgjohannsen/mltlsat
    
    See https://link.springer.com/chapter/10.1007/978-3-030-25543-5_1
    """
    if len(context.atomic_id) == 0:
        log.error("No atomics found while writing SMT, SMT can only be output after compilation", MODULE_CODE)
        return ""
    
    smt_commands: list[str] = []

    smt_commands.append("(set-logic AUFLIA)")
    
    atomic_map: dict[cpt.Expression, str] = {}
    visited: set[int] = set()
    for atomic,id in [(a,i) for a,i in context.atomic_id.items()]:
        atomic_map[atomic] = f"a{id}"
        if id in visited:
            continue
        visited.add(id)
        smt_commands.append(f"(declare-fun {atomic_map[atomic]} (Int) Bool)")

    qvar_cnt = 0

    stack: list["tuple[int, cpt.Expression, str, str, str, str]"] = []
    stack.append((0, start, "", "", "len", "0"))

    define_fun = "(define-fun f ((k Int) (len Int)) Bool "

    while len(stack) > 0:
        (seen, expr, qvar_id_1, qvar_id_2, length, loc) = stack.pop()

        if isinstance(expr, cpt.Constant) and expr.value:
            define_fun += f"(and (> {length} 0) true)"
        elif isinstance(expr, cpt.Constant) and not expr.value:
            define_fun += f"(and (> {length} 0) false))"
        elif expr in context.atomic_id:
            define_fun += f"(and (> {length} 0) ({atomic_map[expr]} k))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            if seen == 0:
                define_fun += f"(and (> {length} 0) (not "
                stack.append((seen + 1, expr, "", "", length, loc))
                stack.append((0, expr.children[0], "", "", length, loc))
            else:
                define_fun += "))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            if seen == 0:
                define_fun += f"(and (> {length} 0) (and "
                stack.append((seen + 1, expr, "", "", length, loc))
                [stack.append((0, child, "", "", length, loc)) for child in reversed(expr.children)]
            else:
                define_fun += "))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            if seen == 0:
                define_fun += f"(and (> {length} 0) (or "
                stack.append((seen + 1, expr, "", "", length, loc))
                [stack.append((0, child, "", "", length, loc)) for child in reversed(expr.children)]
            else:
                define_fun += "))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            if seen == 0:
                define_fun += f"(and (> {length} 0) (=> "
                stack.append((seen + 1, expr, "", "", length, loc))
                stack.append((0, expr.children[0], "", "", length, loc))
                stack.append((0, expr.children[1], "", "", length, loc))
            else:
                define_fun += "))"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            if seen == 0:
                define_fun += f"(and (> {length} 0) (= "
                stack.append((seen + 1, expr, "", "", length, loc))
                stack.append((0, expr.children[0], "", "", length, loc))
                stack.append((0, expr.children[1], "", "", length, loc))
            else:
                define_fun += "))"
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            if seen == 0:
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub
                
                qvar = f"v{qvar_cnt}"
                qvar_cnt += 1

                define_fun += (
                    f"(and (> {length} {lb}) (forall (({qvar} Int)) (=> (and (<= (+ {loc} {lb}) {qvar}) (<= {qvar} (+ {ub} {loc}))) "
                )
                
                stack.append((seen + 1, expr, qvar, "", length, loc))
                stack.append((0, expr.children[0], "", "", f"(- {length} {qvar})", qvar))
            else:
                define_fun += ")))"
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            if seen == 0:
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub
                
                qvar = f"v{qvar_cnt}"
                qvar_cnt += 1

                define_fun += (
                    f"(and (> {length} {lb}) (exists (({qvar} Int)) (and (and (<= (+ {loc} {lb}) {qvar}) (<= {qvar} (+ {ub} {loc}))) "
                )

                stack.append((seen + 1, expr, qvar, "", length, loc))
                stack.append((0, expr.children[0], "", "", f"(- {length} {qvar})", qvar))
            else:
                define_fun += ")))"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            if seen == 0:
                expr = cast(cpt.TemporalOperator, expr)
                lb = expr.interval.lb
                ub = expr.interval.ub
                
                qvar1 = f"v{qvar_cnt}"
                qvar_cnt += 1
                qvar2 = f"v{qvar_cnt}"
                qvar_cnt += 1

                define_fun += (
                    f"(and (> {length} {lb}) (exists (({qvar1} Int)) (and (<= (+ {loc} {lb}) {qvar1}) (<= {qvar1} (+ {ub} {loc})) "
                )

                stack.append((seen + 1, expr, qvar1, qvar2, length, loc))
                stack.append((0, expr.children[0], "", "", f"(- {length} {qvar})", qvar))
                stack.append((seen + 1, expr, qvar1, qvar2, length, loc))
                stack.append((0, expr.children[1], "", "", f"(- {length} {qvar})", qvar))
            elif seen == 1:
                define_fun += f"(forall (({qvar_id_2} Int)) (=> (and (<= (+ {loc} {lb}) {qvar_id_2}) (< {qvar_id_2} {qvar_id_1})) "
            else:
                define_fun += ")))))"
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(f"Release not implemented for MLTL-SAT\n\t{expr}", MODULE_CODE)
            return ""
        else:
            log.error(f"Bad repr ({expr})", MODULE_CODE)
            return ""
    
    define_fun += ")"
    smt_commands.append(define_fun)

    smt_commands.append("(assert (exists ((len Int)) (f 0 len)))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def to_smt_sat_query(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns a string representing an SMT-LIB2 encoding of the MLTL sat problem.
    
    See https://link.springer.com/chapter/10.1007/978-3-030-25543-5_1
    """
    if len(context.atomic_id) == 0:
        log.error("No atomics found while writing SMT, SMT can only be output after compilation", MODULE_CODE)
        return ""

    smt_commands: list[str] = []
    
    smt_commands.append("(set-logic AUFLIA)")

    atomic_map: dict[cpt.Expression, str] = {}
    for atomic,id in context.atomic_id.items():
        atomic_map[atomic] = f"f_a{id}"
        smt_commands.append(f"(declare-fun {atomic_map[atomic]} (Int) Bool)")

    expr_map: dict[cpt.Expression, str] = {}
    cnt = 0

    for expr in cpt.postorder(start, context):
        if expr in expr_map:
            continue

        expr_id = f"f_e{cnt}"
        cnt += 1
        expr_map[expr] = expr_id

        fun_signature = f"define-fun {expr_id} ((k Int) (len Int)) Bool"

        if isinstance(expr, cpt.Constant) and expr.value:
            smt_commands.append(f"({fun_signature} (and (> len k) true))")
        elif isinstance(expr, cpt.Constant) and not expr.value:
            smt_commands.append(f"({fun_signature} (and (> len k) false))")
        elif expr in context.atomic_id:
            smt_commands.append(f"({fun_signature} (and (> len k) ({atomic_map[expr]} k)))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            smt_commands.append(f"({fun_signature} (and (> len k) (not ({expr_map[expr.children[0]]} k len))))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            operands = " ".join([f'({expr_map[child]} k len)' for child in expr.children])
            smt_commands.append(f"({fun_signature} (and (> len k) (and {operands})))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            operands = " ".join([f'({expr_map[child]} k len)' for child in expr.children])
            smt_commands.append(f"({fun_signature} (and (> len k) (or {operands})))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            smt_commands.append(f"({fun_signature} (and (> len k) (=> ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))")
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            smt_commands.append(f"({fun_signature} (and (> len k) (= ({expr_map[expr.children[0]]} k len) ({expr_map[expr.children[1]]} k len))))")
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (forall ((i Int)) (=> (and (<= (+ {lb} k) i) (<= i (+ {ub} k))) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (and (<= (+ {lb} k) i) (<= i (+ {ub} k))) ({expr_map[expr.children[0]]} i len)))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            lb = expr.interval.lb
            ub = expr.interval.ub
            smt_commands.append(
                f"({fun_signature} (and (> len (+ {lb} k)) (exists ((i Int)) (and (<= (+ {lb} k) i) (<= i (+ {ub} k)) ({expr_map[expr.children[1]]} i (- len i)) (forall ((j Int)) (=> (and (<= (+ {lb} k) j) (< j i)) ({expr_map[expr.children[0]]} j len)))))))"
            )
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            log.error(f"Release not implemented for MLTL-SAT\n\t{expr}", MODULE_CODE)
            return ""
        else:
            log.error(f"Bad repr ({expr})", MODULE_CODE)
            return ""
        
    smt_commands.append(f"(assert (exists ((len Int)) ({expr_map[expr]} 0 len)))")
    smt_commands.append("(check-sat)")

    smt = "\n".join(smt_commands)

    return smt


def check_sat_expr(expr: cpt.Expression, context: cpt.Context) -> SatResult:
    """Returns result of running SMT solver on the SMT encoding of `expr`."""
    log.debug(f"Checking satisfiability:\n\t{repr(expr)}", MODULE_CODE)

    if not check_solver_installed(Z3):
        log.error("z3 not found", MODULE_CODE)
        return SatResult.UNKNOWN

    if WORK_DIR.is_file():
        WORK_DIR.unlink()

    if not WORK_DIR.is_dir():
        WORK_DIR.mkdir()

    smt = to_smt_sat_query(expr, context)

    smt_file_path = WORK_DIR / "__tmp__.smt"
    with open(smt_file_path, "w") as f:
        f.write(smt)

    command = [Z3, str(smt_file_path)]
    log.debug(f"Running '{' '.join(command)}'", MODULE_CODE)
    proc = subprocess.run(command, capture_output=True)

    if proc.stdout.decode().find("unsat") > -1:
        log.debug("unsat", MODULE_CODE)
        return SatResult.UNSAT
    elif proc.stdout.decode().find("sat") > -1:
        log.debug("sat", MODULE_CODE)
        return SatResult.SAT
    else:
        log.debug("unsat", MODULE_CODE)
        return SatResult.UNKNOWN


def check_sat(program: cpt.Program, context: cpt.Context) -> "dict[cpt.Specification, SatResult]":
    """Runs an SMT solver (Z3 by default) on the SMT encoding of the MLTL formulas in `program`."""
    if not check_solver_installed(Z3):
        log.error("z3 not found", MODULE_CODE)
        return {}

    if WORK_DIR.is_file():
        WORK_DIR.unlink()
    elif WORK_DIR.is_dir():
        shutil.rmtree(WORK_DIR)
    
    WORK_DIR.mkdir()

    results: dict[cpt.Specification, SatResult] = {}
    
    for spec in program.ft_spec_set.get_specs():
        if isinstance(spec, cpt.Contract):
            log.warning("Found contract, skipping", MODULE_CODE)
            continue
            
        expr = spec.get_expr()
        results[spec] = check_sat_expr(expr, context)

    shutil.rmtree(WORK_DIR)
        
    return results


def check_equiv(expr1: cpt.Expression, expr2: cpt.Expression, context: cpt.Context) -> Optional[bool]:
    """Returns true if `expr1` is equivalent to `expr2`, false if they are not, and None if the check timed our or failed in some other way.
    
    To check equivalence, this function encodes the formula `!(expr1 <-> expr2)`: if this formula is unsatisfiable it means there is no trace `pi` such that `pi |= expr` and `pi |/= expr` or vice versa.  
    """
    log.debug(f"Checking equivalence:\n\t{repr(expr1)}\n\t\t<->\n\t{repr(expr2)}", MODULE_CODE)

    neg_equiv_expr = cpt.Operator.LogicalNegate(expr1.loc, cpt.Operator.LogicalIff(expr1.loc, expr1, expr2))

    result = check_sat_expr(neg_equiv_expr, context)

    if result is SatResult.SAT:
        log.debug("Not equivalent", MODULE_CODE)
        return False
    elif result is SatResult.UNSAT:
        log.debug("Equivalent", MODULE_CODE)
        return True
    else:
        log.debug("Unknown", MODULE_CODE)
        return None

