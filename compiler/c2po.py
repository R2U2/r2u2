import argparse
import sys

import c2po.main
import c2po.options

parser = argparse.ArgumentParser()
parser.add_argument(
    "spec", 
    help="specification file (either .c2po or .mltl)"
)
parser.add_argument(
    "--trace",
    default=c2po.options.DEFAULTS["trace_filename"],
    help="csv file where variable names are mapped to signal order using file header",
)
parser.add_argument(
    "--map",
    default=c2po.options.DEFAULTS["map_filename"],
    help="map file where variable names are mapped to signal order",
)
parser.add_argument(
    "-q",
    "--quiet",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["quiet"],
    help="disable output",
)
parser.add_argument(
    "-v",
    "--verbose",
    dest="log_level",
    action="count",
    default=c2po.options.DEFAULTS["log_level"],
    help="logging verbosity, pass twice for trace logging",
)
parser.add_argument(
    "--debug",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["debug"],
    help="set debug mode, implies trace logging",
)
parser.add_argument(
    "--stats",
    default=c2po.options.DEFAULTS["stats"],
    help="stats output format string",
)
parser.add_argument(
    "--impl",
    default=c2po.options.DEFAULTS["impl_str"],
    choices=["c", "rust", "cpp", "vhdl"],
    help="target R2U2 implementation version (default: %(default)s)",
)
parser.add_argument(
    "-o",
    "--output",
    default=c2po.options.DEFAULTS["output_filename"],
    help="location where specification binary will be written",
)
parser.add_argument(
    "--int-width",
    default=c2po.options.DEFAULTS["int_width"],
    type=int,
    help="bit width for integer types (default: %(default)s)",
)
parser.add_argument(
    "--int-signed",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["int_is_signed"],
    help="signed-ness of int types (default: %(default)s)",
)
parser.add_argument(
    "--float-width",
    default=c2po.options.DEFAULTS["float_width"],
    help="bit width for floating point types (default: %(default)s)",
)
parser.add_argument(
    "--mission-time",
    type=int,
    default=c2po.options.DEFAULTS["mission_time"],
    help="mission time, overriding inference from a trace file if present",
)
parser.add_argument(
    "--scq-constant",
    type=int,
    default=c2po.options.DEFAULTS["scq_constant"],
    help="increase the SCQ sizes of all nodes by this constant",
)
parser.add_argument(
    "-bz", 
    "--booleanizer", 
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["enable_booleanizer"],
    help="enable booleanizer"
)
parser.add_argument(
    "-p", 
    "--parse", 
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["only_parse"],
    help="run only the parser"
)
parser.add_argument(
    "-tc",
    "--type-check",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["only_type_check"],
    help="run only the parser and type checker",
)
parser.add_argument(
    "-c",
    "--compile",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["only_compile"],
    help="run only the parser, type checker, and passes",
)
parser.add_argument(
    "--simulate-mode",
    type=str,
    choices=[member.value for member in c2po.options.SimulateMode],
    default=c2po.options.DEFAULTS["simulate_mode_str"],
    help="simulation mode (default: %(default)s)",
)
parser.add_argument( 
    "--simulate-k",
    type=int,
    default=c2po.options.DEFAULTS["simulate_k"],
    help="simulate the specification for k time steps (default: %(default)s)",
)
parser.add_argument( 
    "--simulate-constraints",
    type=str,
    help="filename to read simulation constraints from",
)
parser.add_argument(
    "--aux",
    action=argparse.BooleanOptionalAction,
    default=c2po.options.DEFAULTS["enable_aux"],
    help="enable aux data (e.g., contract status and specification naming)",
)
parser.add_argument(
    "--cse", 
    action=argparse.BooleanOptionalAction, 
    default=c2po.options.DEFAULTS["enable_cse"],
    help="enable CSE optimization"
)
parser.add_argument(
    "--rewrite",
    action=argparse.BooleanOptionalAction, 
    default=c2po.options.DEFAULTS["enable_rewrite"],
    help="enable MLTL rewrite rule optimizations",
)
parser.add_argument(
    "--extops", 
    action=argparse.BooleanOptionalAction, 
    default=c2po.options.DEFAULTS["enable_extops"],
    help="enable extended operations"
)
parser.add_argument(
    "--nnf", 
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["enable_nnf"],
    help="enable negation normal form"
)
parser.add_argument(
    "--bnf",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["enable_bnf"],
    help="enable boolean normal form"
)
parser.add_argument(
    "--eqsat", 
    action=argparse.BooleanOptionalAction, 
    default=c2po.options.DEFAULTS["enable_eqsat"],
    help="enable equality saturation (default: %(default)s)"
)
parser.add_argument(
    "--egglog-path", 
    default=c2po.options.DEFAULTS["egglog_path"],
    help="path to egglog executable, default assumes egglog is in PATH (default: %(default)s)"
)
parser.add_argument(
    "--eqsat-max-time", 
    type=int, 
    default=c2po.options.DEFAULTS["eqsat_max_time"], 
    help="set the maximum time to allow for egglog in seconds (default: %(default)s)"
)
parser.add_argument(
    "--eqsat-max-memory", 
    type=int, 
    default=c2po.options.DEFAULTS["eqsat_max_memory"], 
    help="set the maximum memory to allow for egglog in MB, use 0 for no maximum (default: %(default)s)"
)
parser.add_argument(
    "--check-sat", 
    action=argparse.BooleanOptionalAction, 
    default=c2po.options.DEFAULTS["enable_sat"],
    help="enable satisfiability checking of future-time formulas (default: %(default)s)"
)
parser.add_argument(
    "--smt-solver", 
    default=c2po.options.DEFAULTS["smt_solver_path"],
    help="path to SMTLIB2-compliant executable, default assumes z3 is in PATH (default: %(default)s)"
)
parser.add_argument(
    "--smt-encoding", 
    default=c2po.options.DEFAULTS["smt_encoding_str"], 
    choices=[member.value for member in c2po.options.SMTTheories],
    help="specify the SMT encoding to use for satisfiability checking (default: %(default)s)"
)
parser.add_argument(
    "--smt-option", 
    action="append", 
    default=[],
    help="additional option to pass to the SMT solver, can be specified multiple times (example: --smt-option=\"--opt-1\" --smt-option=\"--opt-2\")"
)
parser.add_argument(
    "--smt-max-time", 
    type=int, 
    default=c2po.options.DEFAULTS["smt_max_time"], 
    help="set the total maximum time to allow for SMT calls in seconds (default: %(default)s)"
)
parser.add_argument(
    "--smt-max-memory", 
    type=int, 
    default=c2po.options.DEFAULTS["smt_max_memory"], 
    help="set the total maximum memory to allow for SMT calls in MB, use 0 for no maximum (default: %(default)s)"
)
parser.add_argument(
    "--write-bounds",
    help="location to write either bounds.h or config.toml file (depending on impl)",
)
parser.add_argument(
    "--write-c2po",
    help="location to write final program in C2PO input format",
)
parser.add_argument(
    "--write-mltl",
    help="location to write final program in MLTL standard format",
)
parser.add_argument(
    "--write-prefix",
    help="location to write final program in prefix notation",
)
parser.add_argument(
    "--write-pickle",
    help="location to write pickled final program",
)
parser.add_argument(
    "--write-smt",
    help="location to write SMT encoding of FT formulas",
)
parser.add_argument(
    "--copyback", 
    help="location of directory to copy workdir contents upon termination"
)

args = parser.parse_args()

opts = c2po.options.Options(
    spec_filename=args.spec,
    trace_filename=args.trace,
    map_filename=args.map,
    output_filename=args.output,
    impl_str=args.impl,
    mission_time=args.mission_time,
    scq_constant=args.scq_constant,
    int_width=args.int_width,
    int_is_signed=args.int_signed,
    float_width=args.float_width,
    only_parse=args.parse,
    only_type_check=args.type_check,
    only_compile=args.compile,
    simulate_mode_str=args.simulate_mode,
    simulate_k=args.simulate_k,
    simulate_constraints=args.simulate_constraints,
    enable_aux=args.aux,
    enable_booleanizer=args.booleanizer,
    enable_extops=args.extops,
    enable_nnf=args.nnf,
    enable_bnf=args.bnf,
    enable_rewrite=args.rewrite,
    enable_eqsat=args.eqsat,
    enable_cse=args.cse,
    enable_sat=args.check_sat,
    write_bounds_filename=args.write_bounds,
    egglog_path=args.egglog_path,
    eqsat_max_time=args.eqsat_max_time,
    eqsat_max_memory=args.eqsat_max_memory,
    smt_solver_path=args.smt_solver,
    smt_encoding_str=args.smt_encoding,
    smt_options=args.smt_option,
    smt_max_time=args.smt_max_time,
    smt_max_memory=args.smt_max_memory,
    write_c2po_filename=args.write_c2po,
    write_prefix_filename=args.write_prefix,
    write_mltl_filename=args.write_mltl,
    write_pickle_filename=args.write_pickle,
    write_smt_dirname=args.write_smt,
    copyback_dirname=args.copyback,
    stats_format_str=args.stats,
    debug=args.debug,
    log_level=args.log_level,
    quiet=args.quiet,
)

return_code = c2po.main.main(opts)
sys.exit(return_code.value)
