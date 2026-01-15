import argparse
import sys
import c2po.main
import c2po.log
import c2po.sat

parser = argparse.ArgumentParser(description="C2PO - Configuration Compiler for Property Organization")
parser.add_argument(
    "--version",
    action="version",
    version=f"C2PO v{c2po.log.VERSION}",
    help="print version and exit",
)
parser.add_argument(
    "-s",
    "--script",
    type=str,
    help="script file to execute, ignores all other arguments",
)
parser.add_argument(
    "-i",
    "--interactive",
    action="store_const",
    const=True,
    help="run in interactive mode, ignores all other arguments",
)
parser.add_argument(
    "--spec", 
    help="specification file (either .c2po, .mltl, or .equiv)"
)
parser.add_argument(
    "--trace",
    type=str,
    help="csv file where variable names are mapped to signal order using file header",
)
parser.add_argument(
    "--map",
    type=str,
    help="map file where variable names are mapped to signal order",
)
parser.add_argument(
    "-o",
    "--output",
    type=str,
    default="spec.bin",
    help="location where specification binary will be written (default: %(default)s)",
)
parser.add_argument(
    "-q",
    "--quiet",
    action="store_const",
    const=True,
    help="disable output",
)
parser.add_argument(
    "-v",
    "--verbose",
    dest="log_level",
    action="count",
    help="logging verbosity, pass twice for trace logging",
)
parser.add_argument(
    "--debug",
    action="store_const",
    const=True,
    help="set debug mode, implies trace logging",
)
parser.add_argument(
    "-p", 
    "--parse", 
    action="store_const",
    const=True,
    default=False,
    help="run only the parser"
)
parser.add_argument(
    "-tc",
    "--type-check",
    action="store_const",
    const=True,
    default=False,
    help="run only the parser and type checker",
)
parser.add_argument(
    "-c",
    "--compile",
    action="store_const",
    const=True,
    default=False,
    help="run only the parser, type checker, and passes",
)
parser.add_argument(
    "--mission-time",
    type=int,
    default=-1,
    help="mission time, overriding inference from a trace file if present",
)
parser.add_argument(
    "--scq-constant",
    type=int,
    default=0,
    help="increase the SCQ sizes of all nodes by this constant",
)
parser.add_argument(
    "-bz", 
    "--booleanizer", 
    action="store_const",
    const=True,
    default=False,
    help="enable booleanizer"
)
parser.add_argument(
    "--aux",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable aux data (e.g., contract status and specification naming)",
)
parser.add_argument(
    "--cse", 
    action=argparse.BooleanOptionalAction, 
    default=True,
    help="enable CSE optimization"
)
parser.add_argument(
    "--rewrite",
    action=argparse.BooleanOptionalAction, 
    default=True,
    help="enable MLTL rewrite rule optimizations",
)
parser.add_argument(
    "--extops", 
    action=argparse.BooleanOptionalAction, 
    default=False,
    help="enable extended operations"
)
parser.add_argument(
    "--eqsat", 
    action=argparse.BooleanOptionalAction, 
    default=False,
    help="enable equality saturation"
)
parser.add_argument(
    "--eqsat-check-equiv",  
    action=argparse.BooleanOptionalAction, 
    default=False,
    help="enable equivalence checking of equality saturation results"
)
parser.add_argument(
    "--eqsat-const-folding",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable const folding rewrite rule for equality saturation"
)
parser.add_argument(
    "--eqsat-associative",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable associative rewrite rule for equality saturation"
)
parser.add_argument(
    "--eqsat-commutative",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable commutative rewrite rule for equality saturation"
)
parser.add_argument(
    "--eqsat-multi-arity",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable multi-arity rewrite rule for equality saturation"
)
parser.add_argument(
    "--eqsat-logical",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable logical rewrite rule for equality saturation"
)
parser.add_argument(
    "--eqsat-temporal",
    action=argparse.BooleanOptionalAction,
    default=True,
    help="enable temporal rewrite rule for equality saturation"
)
parser.add_argument(
    "--eqsat-max-time", 
    type=int, 
    default=5, 
    help="set the maximum time to allow for egglog in seconds (default: %(default)s)"
)
parser.add_argument(
    "--eqsat-max-memory", 
    type=int, 
    default=0, 
    help="set the maximum memory to allow for egglog in MB, use 0 for no maximum (default: %(default)s)"
)
parser.add_argument(
    "--egglog-path", 
    default=None,
    help="path to egglog executable, if not set will search PATH"
)
parser.add_argument(
    "--check-sat", 
    action=argparse.BooleanOptionalAction, 
    default=False,
    help="enable satisfiability checking of future-time formulas"
)
parser.add_argument(
    "--smt-encoding", 
    type=str,
    default=c2po.sat.SMTTheory.UFLIA.value, 
    choices=[v.value for v in c2po.sat.SMTTheory],
    help="specify the SMT encoding to use for satisfiability checking (default: %(default)s)"
)
parser.add_argument(
    "--smt-max-time", 
    type=int, 
    default=5, 
    help="set the total maximum time to allow for SMT calls in seconds (default: %(default)s)"
)
parser.add_argument(
    "--smt-max-memory", 
    type=int, 
    default=0, 
    help="set the total maximum memory to allow for SMT calls in MB, use 0 for no maximum (default: %(default)s)"
)
parser.add_argument(
    "--smt-solver", 
    type=str,
    help="path to SMTLIB2-compliant executable, if not set will search for one in PATH"
)

args = parser.parse_args()

if args.script:
    return_code = c2po.main.script(args.script)
    sys.exit(return_code.value)
elif args.interactive:
    return_code = c2po.main.interactive()
    sys.exit(return_code.value)
elif args.spec:
    return_code = c2po.main.cli(
        spec_filename=args.spec,
        trace_filename=args.trace,
        map_filename=args.map,
        output_filename=args.output,
        quiet=args.quiet,
        debug=args.debug,
        only_parse=args.parse,
        only_type_check=args.type_check,
        only_compile=args.compile,
        mission_time=args.mission_time,
        scq_constant=args.scq_constant,
        enable_booleanizer=args.booleanizer,
        enable_aux=args.aux,
        enable_cse=args.cse,
        enable_rewrite=args.rewrite,
        enable_extops=args.extops,
        enable_eqsat=args.eqsat,
        enable_eqsat_equiv_check=args.eqsat_check_equiv,
        enable_eqsat_const_folding=args.eqsat_const_folding,
        enable_eqsat_associative=args.eqsat_associative,
        enable_eqsat_commutative=args.eqsat_commutative,
        enable_eqsat_multi_arity=args.eqsat_multi_arity,
        enable_eqsat_logical=args.eqsat_logical,
        enable_eqsat_temporal=args.eqsat_temporal,
        eqsat_max_time=args.eqsat_max_time,
        eqsat_max_memory=args.eqsat_max_memory,
        egglog_path=args.egglog_path,
        check_sat=args.check_sat,
        smt_theory=args.smt_encoding,
        smt_max_time=args.smt_max_time,
        smt_max_memory=args.smt_max_memory,
        smt_solver_path=args.smt_solver,
    )
    sys.exit(return_code.value)
else:
    parser.print_help()
    sys.exit(1)
