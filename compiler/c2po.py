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
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["stats"],
    help="enable stat output",
)
parser.add_argument(
    "--impl",
    default=c2po.options.DEFAULTS["impl_str"],
    choices=["c", "rust", "cpp", "vhdl"],
    help=f"target R2U2 implementation version (default: {c2po.options.DEFAULTS['impl_str']})",
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
    help=f"bit width for integer types (default: {c2po.options.DEFAULTS['int_width']})",
)
parser.add_argument(
    "--int-signed",
    action="store_const",
    const=True,
    default=c2po.options.DEFAULTS["int_is_signed"],
    help=f"signed-ness of int types (default: {c2po.options.DEFAULTS['int_is_signed']})",
)
parser.add_argument(
    "--float-width",
    default=c2po.options.DEFAULTS["float_width"],
    help=f"bit width for floating point types (default: {c2po.options.DEFAULTS['float_width']})",
)
parser.add_argument(
    "--mission-time",
    type=int,
    default=c2po.options.DEFAULTS["mission_time"],
    help="mission time, overriding inference from a trace file if present",
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
    help=f"enable equality saturation (default: {c2po.options.DEFAULTS['enable_eqsat']})"
)
parser.add_argument(
    "--egglog-path", 
    default=c2po.options.DEFAULTS["egglog"],
    help=f"path to egglog executable, default assumes egglog is in PATH (default: {c2po.options.DEFAULTS['egglog']})"
)
parser.add_argument(
    "--eqsat-max-time", 
    type=int, 
    default=c2po.options.DEFAULTS["eqsat_max_time"], 
    help=f"set the maximum time to allow for egglog in seconds (default: {c2po.options.DEFAULTS['eqsat_max_time']})"
)
parser.add_argument(
    "--eqsat-max-memory", 
    type=int, 
    default=c2po.options.DEFAULTS["eqsat_max_memory"], 
    help=f"set the maximum memory to allow for egglog in MB, use 0 for no maximum (default: {c2po.options.DEFAULTS['eqsat_max_memory']})"
)
parser.add_argument(
    "--check-sat", 
    action=argparse.BooleanOptionalAction, 
    default=c2po.options.DEFAULTS["enable_sat"],
    help=f"enable satisfiability checking of future-time formulas (default: {c2po.options.DEFAULTS['enable_sat']})"
)
parser.add_argument(
    "--smt-solver", 
    default=c2po.options.DEFAULTS["smt_solver"],
    help=f"path to SMTLIB2-compliant executable, default assumes z3 is in PATH (default: {c2po.options.DEFAULTS['smt_solver']})"
)
parser.add_argument(
    "--smt-encoding", 
    default=c2po.options.DEFAULTS["smt_encoding_str"], 
    choices=[member.value for member in c2po.options.SMTTheories],
    help=f"specify the SMT encoding to use for satisfiability checking (default: {c2po.options.DEFAULTS['smt_encoding_str']})"
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
    help=f"set the total maximum time to allow for SMT calls in seconds (default: {c2po.options.DEFAULTS['smt_max_time']})"
)
parser.add_argument(
    "--smt-max-memory", 
    type=int, 
    default=c2po.options.DEFAULTS["smt_max_memory"], 
    help=f"set the total maximum memory to allow for SMT calls in MB, use 0 for no maximum (default: {c2po.options.DEFAULTS['smt_max_memory']})"
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
parser.add_argument(
    "--write-hydra", 
    help="location to write hydra encoding of FT formulas"
)

parser.add_argument("--bvmon", action="store_true", help="bvmon mode")
parser.add_argument("--bvmon-word-size", type=int, default=c2po.options.DEFAULTS["bvmon_word_size"], help="bvmon word size")
parser.add_argument("--bvmon-nsigs", type=int, help="number of signals in bvmon encoding")

args = parser.parse_args()

opts = c2po.options.Options(
    spec_filename=args.spec,
    trace_filename=args.trace,
    map_filename=args.map,
    output_filename=args.output,
    impl_str=args.impl,
    mission_time=args.mission_time,
    int_width=args.int_width,
    int_is_signed=args.int_signed,
    float_width=args.float_width,
    only_parse=args.parse,
    only_type_check=args.type_check,
    only_compile=args.compile,
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
    egglog=args.egglog_path,
    eqsat_max_time=args.eqsat_max_time,
    eqsat_max_memory=args.eqsat_max_memory,
    smt_solver=args.smt_solver,
    smt_encoding_str=args.smt_encoding,
    smt_options=args.smt_option,
    smt_max_time=args.smt_max_time,
    smt_max_memory=args.smt_max_memory,
    write_c2po_filename=args.write_c2po,
    write_prefix_filename=args.write_prefix,
    write_mltl_filename=args.write_mltl,
    write_pickle_filename=args.write_pickle,
    write_smt_dirname=args.write_smt,
    write_hydra_filename=args.write_hydra,
    copyback_dirname=args.copyback,
    stats=args.stats,
    debug=args.debug,
    log_level=args.log_level,
    quiet=args.quiet,
    enable_bvmon=args.bvmon,
    bvmon_word_size=args.bvmon_word_size,
    bvmon_nsigs=args.bvmon_nsigs
)

return_code = c2po.main.main(opts)
sys.exit(return_code.value)
