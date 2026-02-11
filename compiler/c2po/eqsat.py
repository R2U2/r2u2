"""
Module for computing the optimal equivalent expression with respect to SCQ sizing using egglog.
"""
from __future__ import annotations
import subprocess
import shutil
import pathlib
import tempfile
import json
from typing import cast, Any, Optional
from c2po import cpt, log, util, types, sat, command, parse_egglog_output

try:
    from c2po import egraph
except ImportError:
    egraph = None

SRC_DIR = pathlib.Path(__file__).parent
EGGLOG_DIR = SRC_DIR / "egglog"
HEURISTIC_DIR = EGGLOG_DIR / "heuristic"
OPTIMAL_DIR = EGGLOG_DIR / "optimal"
REWRITES_DIR = EGGLOG_DIR / "rewrites"
COMPLETE_REWRITE_DIR = REWRITES_DIR / "complete"
INCOMPLETE_REWRITE_DIR = REWRITES_DIR / "incomplete"

HEURISITIC_EXTRACTION_PATHS = [
    HEURISTIC_DIR / "mltl.egg",
    HEURISTIC_DIR / "wpd.egg",
    HEURISTIC_DIR / "bpd.egg",
]

HEURISTIC_EXTENDED_COST_PATH = HEURISTIC_DIR / "cost_extended.egg"
HUERISTIC_COST_PATH = HEURISTIC_DIR / "cost.egg"

OPTIMAL_EXTRACTION_PATHS = [
    OPTIMAL_DIR / "mltl.egg"
]

COMPLETE_REWRITE_PATHS = {
    "associative": REWRITES_DIR / "associative.egg",
    "commutative": REWRITES_DIR / "commutative.egg",
    "multi_arity": REWRITES_DIR / "multi_arity.egg",
    "const_folding": COMPLETE_REWRITE_DIR / "const_folding.egg",
    "temporal": COMPLETE_REWRITE_DIR / "temporal.egg",
}

INCOMPLETE_REWRITE_PATHS = {
    "associative": REWRITES_DIR / "associative.egg",
    "commutative": REWRITES_DIR / "commutative.egg",
    "multi_arity": REWRITES_DIR / "multi_arity.egg",
    "const_folding": INCOMPLETE_REWRITE_DIR / "const_folding.egg",
    "temporal": INCOMPLETE_REWRITE_DIR / "temporal.egg",
}

def find_egglog(context: cpt.Context, use_experimental: bool = False) -> Optional[str]:
    """Find egglog executable by checking the context first, then checking PATH, then compiler/deps/egglog[-experimental]/target/release.

    Args:
        `use_experimental`: Whether to check for egglog-experimental executable (default: False)

    Returns:
        The path to egglog if found, otherwise returns None.
    """
    # First, check if the egglog path is set in the context and is executable
    if context.egglog_path is not None and util.check_executable(context.egglog_path):
        return context.egglog_path

    # First, check if 'egglog' or 'egglog-experimental' is in PATH
    egglog_in_path = shutil.which(
        "egglog" if not use_experimental else "egglog-experimental"
    )
    if egglog_in_path is not None and util.check_executable(egglog_in_path):
        return egglog_in_path

    # If not in PATH, check in compiler/deps/egglog[-experimental]/target/release
    compiler_dir = pathlib.Path(__file__).parent.parent
    deps_path = (
        compiler_dir
        / "deps"
        / ("egglog" if not use_experimental else "egglog-experimental")
        / "target"
        / "release"
        / ("egglog" if not use_experimental else "egglog-experimental")
    )
    if util.check_executable(str(deps_path)):
        return str(deps_path)
    return None
    
def to_egglog(
    start: cpt.Expression, context: cpt.Context, options: dict[str, Any]
) -> Optional[str]:
    """Generates the egglog encoding for `start` and returns it as a string.
    
    `options` is a dictionary of options for the writing.
    - `heuristic-extraction`: Whether to enable heuristic extraction of the egglog output
    - `rewrites`: The set of rewrites to enable
        - `incomplete`: Enable the incomplete set of rewrites (default)
        - `complete`: Enable the complete set of rewrites
    - `associative`: Whether to enable associative rewrites
    - `commutative`: Whether to enable commutative rewrites
    - `multi-arity`: Whether to enable multi-arity rewrites
    - `const-folding`: Whether to enable const folding
    - `temporal`: Whether to enable temporal rewrites
    - `extended`: Whether to enable extended operator rewrites

    Returns:
        The egglog encoding for `start`, or None if an error occurs.
    """
    egglog = ""

    for path in (
        HEURISITIC_EXTRACTION_PATHS
        if options["heuristic_extraction"]
        else OPTIMAL_EXTRACTION_PATHS
    ):
        with open(path, "r") as f:
            egglog += f.read()
            egglog += "\n\n"

    if options["extended"] and options["heuristic_extraction"]:
        with open(HEURISTIC_EXTENDED_COST_PATH, "r") as f:
            egglog += f.read()
            egglog += "\n\n"
    elif options["heuristic_extraction"]:
        with open(HUERISTIC_COST_PATH, "r") as f:
            # To force extraction to avoid extended operators, we set their costs to wpd * 2. 
            # No term in the egraph will have a cost greater than this.
            egglog += f.read().replace("MAX_COST", str(start.wpd * 2))
            egglog += "\n\n"

    if options["rewrites"] == "incomplete":
        for rewrite, path in INCOMPLETE_REWRITE_PATHS.items():
            if options.get(rewrite, False):
                with open(path, "r") as f:
                    egglog += f.read()
                    egglog += "\n\n"
    else:
        for rewrite, path in COMPLETE_REWRITE_PATHS.items():
            if rewrite == "commutative" or rewrite == "associative":
                continue
            if options.get(rewrite, False):
                with open(path, "r") as f:
                    egglog += f.read()
                    egglog += "\n\n"

    start_time = util.get_rusage_time()

    expr_cnt = 0
    expr_map: dict[cpt.Expression, int] = {}

    stack: list["tuple[int, cpt.Expression]"] = []
    stack.append((0, start))
    
    # Assign an integer to every non-Booleanizer expression (that is not an Atomic) in the program
    for expr in cpt.postorder(start, context):
        if (
            expr.engine == types.R2U2Engine.BOOLEANIZER 
            and not isinstance(expr, cpt.Atomic)
        ):
            continue

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

    egglog += "\n"
    egglog += "(run-schedule (saturate mltl-rewrites))\n"
    egglog += "(run-schedule (saturate const-folding))\n"

    if options["heuristic_extraction"]:
        egglog += "(run-schedule (saturate analysis))\n"
        egglog += f"(extract $e{expr_map[start]})\n"

    end_time = util.get_rusage_time()
    context.stats.eqsat_encoding_time = end_time - start_time

    return egglog

def run_egglog(
    egglog_encoding: str,
    max_time: int,
    max_memory: int,
    context: cpt.Context,
    use_experimental_egglog: bool = False,
) -> tuple[str, dict, str, float]:
    """Runs egglog on the given egglog encoding file and returns the result as a string and the time taken.
    
    Args:
        `egglog_encoding`: The egglog encoding to run
        `max_time`: The maximum time to allow for egglog in seconds
        `max_memory`: The maximum memory to allow for egglog in MB, use 0 for no maximum
        `context`: The context to use for finding the egglog executable
        `use_experimental_egglog`: Whether to use the experimental egglog executable

    Returns:
        A tuple containing the egglog output, the status of the egglog run, and the time taken
    """
    egglog_bin = find_egglog(context, use_experimental_egglog) 
    if egglog_bin is None:
        log.error("could not find egglog executable, please set the `egglog-path` option")
        return "", {}, "failure", -1.0

    with tempfile.TemporaryDirectory() as temp_dir:
        egglog_encoding_path = pathlib.Path(temp_dir) / "tmp.egg"
        with open(egglog_encoding_path, "w") as f:
            f.write(egglog_encoding)

        command = [egglog_bin, str(egglog_encoding_path), "--to-json"]
        log.debug(2, f"running command '{' '.join(command)}'")

    start = util.get_rusage_time()
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
        log.warning(MODULE_CODE, f"{context.options.egglog_path} timed out")
        context.stats.eqsat_solver_time = -1.0
        return None
    
    end = util.get_rusage_time()
    stdout = stdout.decode()
    stderr = stderr.decode()

    if proc.returncode:
        log.error(MODULE_CODE, f"Error running egglog\n{stderr}")
        return None

    with open(EGGLOG_OUTPUT, "r") as f:
        egglog_output = json.load(f)

    egraph = EGraph.from_json(egglog_output, spec.get_expr(), context)

    end = util.get_rusage_time()
    context.stats.eqsat_solver_time = end - start

    return egraph
