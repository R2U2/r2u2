"""
Module for computing the optimal equivalent expression with respect to SCQ sizing using egglog.
"""
from __future__ import annotations
import subprocess
import shutil
import pathlib
import tempfile
import json
from typing import cast, Any, Optional, Union
from c2po import cpt, log, util, types, sat, command, parse_egglog_output

try:
    from c2po import egraph
except ImportError:
    log.warning("gurobipy is not installed, please install it and try again")
    egraph = None

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

def find_egglog(experimental: bool = False) -> Optional[str]:
    """Find egglog executable by checking PATH first, then compiler/deps/egglog[-experimental]/target/release.

    Args:
        `experimental`: Whether to check for egglog-experimental executable (default: False)

    Returns:
        The path to egglog if found, otherwise returns None.
    """
    # First, check if 'egglog' or 'egglog-experimental' is in PATH
    egglog_in_path = shutil.which(
        "egglog" if not experimental else "egglog-experimental"
    )
    if egglog_in_path is not None and util.check_executable(egglog_in_path):
        return egglog_in_path

    # If not in PATH, check in compiler/deps/egglog[-experimental]/target/release
    compiler_dir = pathlib.Path(__file__).parent.parent
    deps_path = (
        compiler_dir
        / "deps"
        / ("egglog" if not experimental else "egglog-experimental")
        / "target"
        / "release"
        / ("egglog" if not experimental else "egglog-experimental")
    )
    if deps_path.exists() and deps_path.is_file() and util.check_executable(str(deps_path)):
        return str(deps_path)
    return None
    
def to_egglog(
    start: cpt.Expression, context: cpt.Context, options: dict[str, Any]
) -> Optional[str]:
    """Generates the egglog encoding for `start` and returns it as a string.
    
    `options` is a dictionary of options for the writing.
    - `const-folding`: Whether to enable const folding
    - `associative`: Whether to enable associative rewrites
    - `commutative`: Whether to enable commutative rewrites
    - `multi-arity`: Whether to enable multi-arity rewrites
    - `logical`: Whether to enable logical rewrites
    - `temporal`: Whether to enable temporal rewrites
    - `with-analysis`: Whether to enable analysis and (heuristic) extraction of the egglog output

    Returns:
        The egglog encoding for `start`, or None if an error occurs.
    """
    egglog = ""
    if not options["with_analysis"]:
        with open(SRC_DIR / "egglog" / "mltl_no_analysis.egg", "r") as f:
            egglog += f.read()
    else:
        for path in REQUIRED_PATHS:
            with open(path, "r") as f:
                egglog += f.read()
                egglog += "\n\n"

    for rewrite, path in REWRITE_PATHS.items():
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

    if options["with_analysis"]:
        egglog += "(run-schedule (saturate analysis))\n"
        egglog += f"(extract $e{expr_map[start]})\n"

    end_time = util.get_rusage_time()
    context.stats.eqsat_encoding_time = end_time - start_time

    return egglog

def run_egglog(
    egglog_encoding: str,
    max_time: int,
    max_memory: int,
    with_json: bool = False,
    egglog_bin: Optional[str] = None,
) -> tuple[Union[dict, str], str, float]:
    """Runs egglog on the given egglog encoding file and returns the result as a string and the time taken.
    
    Args:
        `egglog_encoding`: The egglog encoding to run
        `max_time`: The maximum time to allow for egglog in seconds
        `max_memory`: The maximum memory to allow for egglog in MB, use 0 for no maximum
        `with_json`: Whether to return the egglog output as a JSON object
        `egglog_bin`: The path to the egglog executable. If not provided, will be found using `find_egglog()`.

    Returns:
        A tuple containing the egglog output, the status of the egglog run, and the time taken
    """
    if egglog_bin is None:  
        egglog_bin = find_egglog(not with_json) # If we are doing analysis, we need to use the experimental egglog
        if egglog_bin is None:
            log.error("could not find egglog executable, please set the `egglog-bin` option")
            return "", "failure", -1.0

    with tempfile.TemporaryDirectory() as temp_dir:
        egglog_encoding_path = pathlib.Path(temp_dir) / "tmp.egg"
        with open(egglog_encoding_path, "w") as f:
            f.write(egglog_encoding)

        command = [egglog_bin, str(egglog_encoding_path)]
        if with_json:
            command += ["--to-json"]
        log.debug(1, f"running command '{' '.join(command)}'")

        start_time = util.get_rusage_time()
        try:
            proc = subprocess.Popen(
                command,
                preexec_fn=util.set_max_memory_offset(max_memory),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
        except OSError as e:
            log.internal(f"error running command '{' '.join(command)}': {e}")
            return "", "failure", -1.0

        try:
            (stdout, stderr) = proc.communicate(timeout=max_time)
        except subprocess.TimeoutExpired:
            proc.kill()
            log.warning(f"{egglog_bin} timed out")
            return "", "timeout", -1.0

        end_time = util.get_rusage_time()

        if proc.returncode == -6:
            log.error(f"error running egglog (out of memory)\n{stderr.decode()}")
            return "", "memout", -1.0
        elif proc.returncode != 0:
            log.error(f"error running egglog ({proc.returncode})\n{stderr.decode()}")
            return "", "failure", -1.0

        if with_json:
            json_output_path = pathlib.Path(temp_dir) / "tmp.json"
            with open(json_output_path, "r") as f:
                output = json.loads(f.read())
            return output, "ok", end_time - start_time

    return stdout.decode(), "ok", end_time - start_time

def write_eqsat_encoding(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Writes the EQSat encoding for the program to the given file.
    
    `options` is a dictionary of options for the writing.
    - `location`: The path to write the EQSat encoding to
    - `formula`: The formula to write the EQSat encoding for. If not provided, all formulas will be written
    - `with-analysis`: Whether to enable analysis and (heuristic) extraction of the egglog output

    Returns:
        a ReturnCode.SUCCESS if the encoding was written successfully, ReturnCode.ERROR otherwise
    """
    def write_egglog(formula: cpt.Formula, location: pathlib.Path, output_is_dir: bool) -> command.ReturnCode:
        egglog_encoding = to_egglog(formula.get_expr(), context, options)
        if egglog_encoding is None:
            log.error(f"failed to write egglog encoding for {formula.symbol}", formula.loc)
            return command.ReturnCode.ERROR
        egglog_path = location / f"{formula.symbol}.eqsat.egglog" if output_is_dir else location
        with open(egglog_path, "w") as f:
            f.write(egglog_encoding)
        return command.ReturnCode.SUCCESS

    # Setup the output location
    # If the location is a file, we will overwrite it
    # If the location is a directory and already exists, we will write the encodings to it
    # If we only have one encoding and the location is not a directory, we will write it to the location as a file
    location = pathlib.Path(options["location"])
    output_is_dir = False
    if location.is_file():
        location.unlink()
    elif location.is_dir():
        output_is_dir = True

    if options["formula"] is not None:
        formula = program.get_spec(options["formula"])
        if formula is None:
            log.error(f"formula {options['formula']} not found")
            return command.ReturnCode.ERROR
        elif isinstance(formula, cpt.Contract):
            log.error(f"formula {options['formula']} is a contract")
            return command.ReturnCode.ERROR
        return write_egglog(formula, location, output_is_dir)   

    if len(program.ft_spec_set.get_specs()) > 1:
        output_is_dir = True

    if output_is_dir:
        location.mkdir(parents=True, exist_ok=True)

    for formula in program.ft_spec_set.get_specs():
        if isinstance(formula, cpt.Contract):
            log.debug(2, f"found contract {formula.symbol}, skipping")
            continue
        result = write_egglog(formula, location, output_is_dir)
        if result != command.ReturnCode.SUCCESS:
            return result

    return command.ReturnCode.SUCCESS

write_eqsat_encoding_command = command.Command(
    name="write_eqsat_encoding",
    description="Write the EQSat encoding for the program",
    options=[
        {
            "name": "location",
            "description": "The path to write the EQSat encoding to",
            "required": True,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "formula",
            "description": "The formula to write the EQSat encoding for. If not provided, all formulas will be written",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "const-folding",
            "description": "Whether to enable const folding rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "associative",
            "description": "Whether to enable associative rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "commutative",
            "description": "Whether to enable commutative rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "multi-arity",
            "description": "Whether to enable multi-arity rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "temporal",
            "description": "Whether to enable temporal and logical rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "with-analysis",
            "description": "Whether to enable analysis and (heuristic) extraction of the egglog output",
            "required": False,
            "type": bool,
            "default": False,
            "choices": None,
        },
    ],
    func=write_eqsat_encoding,
    guards=[command.COMPUTED_ATOMICS],
)
command.CommandRegistry.register(write_eqsat_encoding_command)

def optimize_eqsat(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """Performs equality saturation using the egglog encodings stored in `context`. Fails if equivalence checking is enabled and the optimized formula is not equivalent to the original formula.
    
    `options` is a dictionary of options for the optimization.
    - `const-folding`: Whether to enable const folding
    - `associative`: Whether to enable associative rewrites
    - `commutative`: Whether to enable commutative rewrites
    - `multi-arity`: Whether to enable multi-arity rewrites
    - `temporal`: Whether to enable temporal rewrites
    - `egglog-max-time`: The maximum time to allow for egglog in seconds
    - `egglog-max-memory`: The maximum memory to allow for egglog in MB, use 0 for no maximum
    - `egglog-bin`: The path to the egglog executable
    - `extraction-method`: The method to use for extraction
        - `heuristic`: Use heuristic extraction (default)
        - `optimal`: Use optimal extraction using Gurobi (requires gurobipy to be installed)
    - `gurobi-max-time`: The maximum time to allow for Gurobi in seconds if `extraction-method` is `optimal`
    - `gurobi-max-memory`: The maximum memory to allow for Gurobi in MB, use 0 for no maximum if `extraction-method` is `optimal`
    - `equiv-smt-encoding-filename`: The path to write the SMT encoding for equivalence checking to
    - `check-equiv`: Whether to check equivalence of the optimized formula
    - `theory`: The SMT theory to use if `check-equiv` is enabled
    - `smt-max-time`: The maximum time to allow for the SMT solver in seconds if `check-equiv` is enabled
    - `smt-max-memory`: The maximum memory to allow for the SMT solver in MB, use 0 for no maximum if `check-equiv` is enabled

    Returns:
        a ReturnCode.SUCCESS if the optimization was successful, ReturnCode.ERROR otherwise
    """
    status = True

    for formula in program.ft_spec_set.get_specs():
        if isinstance(formula, cpt.Contract):
            log.warning("found contract, skipping")
            continue

        if options["extraction_method"] == "optimal":
            options["with_analysis"] = False
        else:
            options["with_analysis"] = True

        egglog_encoding = to_egglog(formula.get_expr(), context, options)
        if egglog_encoding is None:
            log.error(f"failed to generate egglog encoding for {formula.symbol}", formula.loc)
            return command.ReturnCode.ERROR

        old = formula.get_expr()
        egglog_output, status, time = run_egglog(
            egglog_encoding,
            options["egglog_max_time"],
            options["egglog_max_memory"],
            options["extraction_method"] == "optimal", # Have egglog return JSON if we are using optimal extraction
            options["egglog_bin"],
        )
        context.stats.eqsat_solver_time += time
        context.stats.eqsat_solver_status = status
        if status != "ok":
            log.warning(f"eqsat failed for {formula.symbol}, skipping")
            continue

        if options["extraction_method"] == "optimal":
            if egraph is None:
                log.error("gurobipy is not installed, please install it and try again or use `heuristic` extraction")
                return command.ReturnCode.ERROR

            if not isinstance(egglog_output, dict) or "nodes" not in egglog_output:
                log.error(f"error running egglog (no nodes)\n{repr(egglog_output)}")
                return command.ReturnCode.ERROR
            
            egraph_instance = egraph.EGraph.from_json(egglog_output["nodes"], old, context)
            if egraph_instance is None:
                log.error(f"failed to generate EGraph for {formula.symbol}", formula.loc)
                return command.ReturnCode.ERROR

            new = egraph_instance.extract(
                options["gurobi_max_time"],
                options["gurobi_max_memory"],
            )
        else:
            new = parse_egglog_output.parse(str(egglog_output), context, options)

        log.debug(1, f"eqsat result: {repr(new)}")
        if new is None:
            status = False
            continue

        # If equivalence checking is disabled, we can just replace the old expression with the new one
        if not options["check_equiv"]:
            old.replace(new)
            continue

        # Otherwise, we check if the new expression is equivalent to the old expression
        theory = sat.SMTTheory(options["theory"])
        eqsat_smt_encoding = sat.to_smt_equiv(old, new, context, theory, strict=False)
        if eqsat_smt_encoding is None:
            log.error("failed to generate SMT encoding for equivalence", formula.loc)
            return command.ReturnCode.ERROR

        if options["equiv_smt_encoding_filename"] is not None:
            with open(options["equiv_smt_encoding_filename"], "w") as f:
                f.write(eqsat_smt_encoding)

        sat_result = sat.run_smt_solver(
            eqsat_smt_encoding,
            theory,
            options["smt_max_time"],
            options["smt_max_memory"],
            context.stats,
        )

        if sat_result is sat.SatResult.UNSAT:
            log.debug(1, "equality saturation produced equivalent formula")
            equiv_result = "equiv"
            old.replace(new)
        elif sat_result is sat.SatResult.SAT:
            log.warning("equality saturation produced non-equivalent formula, defaulting to non-optimized formula")
            equiv_result = "not-equiv"
            status = False
        else:
            if options["check_equiv"]:
                log.warning("equality saturation could not be validated, still using optimized formula")
            equiv_result = "unknown"
            old.replace(new)

        context.stats.eqsat_equiv_result = equiv_result

    log.debug(1, f"post EQSat:\n{repr(program)}")
    return command.ReturnCode.SUCCESS if status else command.ReturnCode.ERROR

optimize_eqsat_command = command.Command(
    name="optimize_eqsat",
    description="Optimize the program via EQSat",
    options=[
        {
            "name": "const-folding",
            "description": "Whether to enable const folding",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "associative",
            "description": "Whether to enable associative rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "commutative",
            "description": "Whether to enable commutative rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "multi-arity",
            "description": "Whether to enable multi-arity rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "temporal",
            "description": "Whether to enable temporal rewrites",
            "required": False,
            "type": bool,
            "default": True,
            "choices": None,
        },
        {
            "name": "egglog-max-time",
            "description": "The maximum time to allow for egglog in seconds",
            "required": False,
            "type": int,
            "default": 5,
            "choices": None,
        },
        {
            "name": "egglog-max-memory",
            "description": "The maximum memory to allow for egglog in MB, use 0 for no maximum",
            "required": False,
            "type": int,
            "default": 0,
            "choices": None,
        }, 
        {
            "name": "egglog-bin",
            "description": "The path to the egglog executable",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "extraction-method",
            "description": "The method to use for extraction",
            "required": False,
            "type": str,
            "default": "heuristic",
            "choices": ["heuristic", "optimal"],
        },
        {
            "name": "gurobi-max-time",
            "description": "The maximum time to allow for Gurobi in seconds if `extraction-method` is `optimal`",
            "required": False,
            "type": int,
            "default": 10,
            "choices": None,
        },
        {
            "name": "gurobi-max-memory",
            "description": "The maximum memory to allow for Gurobi in MB, use 0 for no maximum if `extraction-method` is `optimal`",
            "required": False,
            "type": int,
            "default": 0,
            "choices": None,
        },
        {
            "name": "check-equiv",
            "description": "Whether to check equivalence of the optimized formula",
            "required": False,
            "type": bool,
            "default": False,
            "choices": None,
        },
        {
            "name": "equiv-smt-encoding-filename",
            "description": "The path to write the SMT encoding for equivalence checking to",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "theory",
            "description": "The SMT theory to use if `check-equiv` is enabled",
            "required": False,
            "type": str,
            "default": sat.SMTTheory.UFLIA.value,
            "choices": [member.value for member in sat.SMTTheory],
        },
        {
            "name": "smt-max-time",
            "description": "The maximum time to allow for the SMT solver in seconds",
            "required": False,
            "type": int,
            "default": 5,
            "choices": None
        }, 
        {
            "name": "smt-max-memory",
            "description": "The maximum memory to allow for the SMT solver in MB, use 0 for no maximum",
            "required": False,
            "type": int,
            "default": 0,
            "choices": None
        },
    ],
    func=optimize_eqsat,
    guards=[command.COMPUTED_ATOMICS],
)
command.CommandRegistry.register(optimize_eqsat_command)
