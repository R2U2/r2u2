"""Module for computing the optimal equivalent expression with respect to SCQ sizing.

We use `egglog` to perform equality saturation and do the extraction of the optimal expression ourselves (due to the complex nature of SCQ sizing). `egglog` does automatic extraction, but works best for cases where the cost of each node can be easily computed using just the children of a given node.
"""
from __future__ import annotations
import subprocess
import pathlib
from typing import Optional, cast

from c2po import cpt, log, util, parse_egglog_output, types

MODULE_CODE = "EQST"
SRC_DIR = pathlib.Path(__file__).parent

REQUIRED_PATHS = [
    SRC_DIR / "egglog" / "mltl.egg",
    SRC_DIR / "egglog" / "wpd.egg",
    SRC_DIR / "egglog" / "bpd.egg",
    SRC_DIR / "egglog" / "cost.egg"
]

REWRITE_PATHS = {
    "const_folding": SRC_DIR / "egglog" / "const_folding.egg",
    "associative": SRC_DIR / "egglog" / "associative.egg",
    "commutative": SRC_DIR / "egglog" / "commutative.egg",
    "multi_arity": SRC_DIR / "egglog" / "multi_arity.egg",
    "logical": SRC_DIR / "egglog" / "logical.egg",
    "temporal": SRC_DIR / "egglog" / "temporal.egg",
}

def check_egglog(egglog: str) -> bool:
    try:
        proc = subprocess.run([egglog, "--version"], capture_output=True)
        return proc.returncode == 0
    except FileNotFoundError:
        return False
    

def to_egglog(start: cpt.Expression, context: cpt.Context) -> str:
    """Returns the egglog encoding for `start`."""
    egglog = ""
    for path in REQUIRED_PATHS:
        with open(path, "r") as f:
            egglog += f.read()

    for rewrite, path in REWRITE_PATHS.items():
        if rewrite in context.options.eqsat_enabled_rewrites:
            with open(path, "r") as f:
                egglog += f.read()
    
    start_time = util.get_rusage_time()

    expr_cnt = 0
    expr_map: dict[cpt.Expression, int] = {}

    stack: list["tuple[int, cpt.Expression]"] = []
    stack.append((0, start))

    for expr in cpt.postorder(start, context):
        expr_map[expr] = expr_cnt
        expr_cnt += 1

        if isinstance(expr, cpt.Constant) and types.is_bool_type(expr.type):
            egglog += f"(let $e{expr_map[expr]} (Bool {expr.symbol.lower()}))\n"
        elif expr in context.atomic_id_map:
            egglog += f'(let $e{expr_map[expr]} (Var "a{context.atomic_id_map[expr]}"))\n'
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_NEGATE):
            egglog += f"(let $e{expr_map[expr]} (Not $e{expr_map[expr.children[0]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_AND):
            arity = len(expr.children)
            egglog += f"(let $e{expr_map[expr]} (And{arity} {' '.join([f'$e{expr_map[c]}' for c in expr.children])}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_OR):
            arity = len(expr.children)
            egglog += f"(let $e{expr_map[expr]} (Or{arity} {' '.join([f'$e{expr_map[c]}' for c in expr.children])}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_IMPLIES):
            egglog += f"(let $e{expr_map[expr]} (Implies $e{expr_map[expr.children[0]]} $e{expr_map[expr.children[1]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.LOGICAL_EQUIV):
            egglog += f"(let $e{expr_map[expr]} (Equiv $e{expr_map[expr.children[0]]} $e{expr_map[expr.children[1]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.GLOBAL):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let $e{expr_map[expr]} (Global (Interval {expr.interval.lb} {expr.interval.ub}) $e{expr_map[expr.children[0]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.FUTURE):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let $e{expr_map[expr]} (Future (Interval {expr.interval.lb} {expr.interval.ub}) $e{expr_map[expr.children[0]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.UNTIL):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let $e{expr_map[expr]} (Until (Interval {expr.interval.lb} {expr.interval.ub}) $e{expr_map[expr.children[0]]} $e{expr_map[expr.children[1]]}))\n"
        elif cpt.is_operator(expr, cpt.OperatorKind.RELEASE):
            expr = cast(cpt.TemporalOperator, expr)
            egglog += f"(let $e{expr_map[expr]} (Release (Interval {expr.interval.lb} {expr.interval.ub}) $e{expr_map[expr.children[0]]} $e{expr_map[expr.children[1]]}))\n"

    egglog = egglog + f"""
(run-schedule (saturate mltl-rewrites))
(run-schedule (saturate const-folding))
(run-schedule (saturate analysis))
(extract $e{expr_map[start]})
"""

    end_time = util.get_rusage_time()
    context.stats.eqsat_encoding_time = end_time - start_time

    return egglog


def run_egglog(egglog_file: pathlib.Path, context: cpt.Context) -> Optional[cpt.Expression]:
    """Runs egglog on the given egglog encoding file and returns the result."""
    command = [context.options.egglog_bin_path, str(egglog_file)]
    log.debug(MODULE_CODE, 1, f"Running command '{' '.join(command)}'")

    start_time = util.get_rusage_time()
    proc = subprocess.Popen(
        command,
        preexec_fn=util.set_max_memory(context.options.eqsat_max_memory),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        (stdout, stderr) = proc.communicate(timeout=context.options.eqsat_max_time)
    except subprocess.TimeoutExpired:
        proc.kill()
        log.warning(MODULE_CODE, f"{context.options.egglog_bin_path} timed out")
        context.stats.eqsat_solver_time = -1.0
        return None

    end_time = util.get_rusage_time()
    context.stats.eqsat_solver_time = end_time - start_time
    
    stdout = stdout.decode()
    stderr = stderr.decode()

    if proc.returncode:
        log.error(MODULE_CODE, f"Error running egglog\n{stderr}")
        return None

    egglog_output = parse_egglog_output.parse(stdout, context)
    if not egglog_output:
        log.error(MODULE_CODE, "Failed to parse egglog output")
        return None

    return egglog_output

