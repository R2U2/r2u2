import argparse
import sys

import c2po.main
import c2po.options

parser = argparse.ArgumentParser()
parser.add_argument("spec",
                    help="specification file (either .c2po .mltl)")

parser.add_argument("--trace",
                    help="CSV file where variable names are mapped to signal order using file header")
parser.add_argument("--map",
                    help="map file where variable names are mapped to signal order")

parser.add_argument("-q","--quiet", action="store_true",
                    help="disable output")
parser.add_argument("-v", "--verbose", dest="log_level", action="count", default=0,
                    help="Logging verbosity, pass twice for trace logging")
parser.add_argument("--debug", action="store_true",
                    help="set debug mode, implies trace logging")
parser.add_argument("--stats", action="store_true",
                    help="enable statistics output")

parser.add_argument("--impl", default="c", choices=["c","cpp","vhdl"],
                    help="specifies target R2U2 implementation version (default: c)")
parser.add_argument("-o", "--output", default="spec.bin",
                    help="specifies location where specification binary will be written")

parser.add_argument("--int-width", default=32, type=int,
                    help="specifies bit width for integer types (default: 32)")
parser.add_argument("--int-signed", action="store_true",
                    help="specifies signedness of int types (default: unsigned)")
parser.add_argument("--float-width", default=32,
                    help="specifies bit width for floating point types (default: 32)")
parser.add_argument("--mission-time", type=int, default=-1,
                    help="specifies mission time, overriding inference from a trace file, if present")

parser.add_argument("-bz", "--booleanizer", action="store_true",
                    help="enable booleanizer")

parser.add_argument("-p", "--parse", action="store_true",
                    help="run only the parser")
parser.add_argument("-tc", "--type-check", action="store_true",
                    help="run only the parser and type checker")
parser.add_argument("-c", "--compile", action="store_true",
                    help="run only the parser, type checker, and passes")

parser.add_argument("--aux", action=argparse.BooleanOptionalAction, default=True,
                    help = "enable aux data (e.g., contract status and specification naming) (default: true)")
parser.add_argument("--cse", action=argparse.BooleanOptionalAction, default=True,
                    help="enable CSE optimization (default: true)")
parser.add_argument("--rewrite", action=argparse.BooleanOptionalAction, default=True,
                    help="enable MLTL rewrite rule optimizations (default: true)")
parser.add_argument("--extops", action=argparse.BooleanOptionalAction, default=False,
                    help="enable extended operations (default: false)")

parser.add_argument("--nnf", action="store_true",
                    help="rewrite final formulas in negation normal form")
parser.add_argument("--bnf", action="store_true",
                    help="rewrite final formulas in boolean normal form")

parser.add_argument("--eqsat", action=argparse.BooleanOptionalAction, default=False,
                    help="enable equality saturation (default: false)")
parser.add_argument("--egglog-path", default="egglog",
                    help="path to egglog executable, default assumes egglog is in PATH (default: egglog)")
parser.add_argument("--eqsat-max-time", type=int, default=3600, 
                    help="set the maximum time to allow for egglog in seconds (default: 3600)")
parser.add_argument("--eqsat-max-memory", type=int, default=0, 
                    help="set the maximum memory to allow for egglog in MB, use 0 for no maximum (default: 0)")

parser.add_argument("--sat", action=argparse.BooleanOptionalAction, default=False,
                    help="enable satisfiability checking of future-time formulas (default: false)")
parser.add_argument("--smt-solver", default="z3",
                    help="path to SMTLIB2-compliant executable, default assumes z3 is in PATH (default: z3)")
parser.add_argument("--smt-encoding", default="uflia", choices=[member.value for member in c2po.options.SMTTheories],
                    help="specify the SMT encoding to use for satisfiability checking (default: uflia)")
parser.add_argument("--smt-option", action="append", default=[],
                    help="additional option to pass to the SMT solver, can be specified multiple times (example: --smt-option=\"--opt-1\" --smt-option=\"--opt-2\")")
parser.add_argument("--smt-max-time", type=int, default=3600, 
                    help="set the total maximum time to allow for SMT calls in seconds (default: 3600)")
parser.add_argument("--smt-max-memory", type=int, default=0, 
                    help="set the total maximum memory to allow for SMT calls in MB, use 0 for no maximum (default: 0)")

parser.add_argument("--write-c2po",
                    help="path to write final program in C2PO input format")
parser.add_argument("--write-mltl",
                    help="path to write final program in MLTL standard format")
parser.add_argument("--write-prefix",
                    help="path to write final program in prefix notation")
parser.add_argument("--write-pickle",
                    help="path to pickle the final program")
parser.add_argument("--write-smt",
                    help="path to write SMT encodings of formulas")
parser.add_argument("--write-hydra",
                    help="path to write first specification in Hydra format")

parser.add_argument("--copyback",
                    help="name of directory to copy workdir contents to upon termination")

parser.add_argument("--bvmon", action="store_true", help="bvmon mode")
parser.add_argument("--bvmon-word-size", type=int, default=8, help="bvmon word size")
parser.add_argument("--bvmon-trace-len", type=int, help="bvmon trace length, encoding is trace length-independent if omitted")

args = parser.parse_args()

return_code = c2po.main.main(
    args.spec, 
    trace_filename=args.trace, 
    map_filename=args.map, 
    impl=args.impl, 
    mission_time=args.mission_time,
    output_filename=args.output, 
    int_width=args.int_width, 
    int_signed=args.int_signed, 
    float_width=args.float_width, 
    only_parse=args.parse,
    only_type_check=args.type_check,
    only_compile=args.compile,
    enable_booleanizer=args.booleanizer, 
    enable_aux=args.aux,
    enable_cse=args.cse, 
    enable_extops=args.extops, 
    enable_rewrite=args.rewrite, 
    enable_eqsat=args.eqsat,
    enable_nnf=args.nnf,
    enable_bnf=args.bnf,
    enable_sat=args.sat,
    egglog_path=args.egglog_path,
    eqsat_max_time=args.eqsat_max_time,
    eqsat_max_memory=args.eqsat_max_memory,
    smt_solver=args.smt_solver,
    smt_options=args.smt_option,
    smt_encoding=args.smt_encoding,
    smt_max_time=args.smt_max_time,
    smt_max_memory=args.smt_max_memory,
    write_c2po_filename=args.write_c2po,
    write_mltl_filename=args.write_mltl,
    write_prefix_filename=args.write_prefix,
    write_pickle_filename=args.write_pickle,
    write_smt_dirname=args.write_smt,
    write_hydra_filename=args.write_hydra,
    copyback_dirname=args.copyback,
    stats=args.stats,
    debug=args.debug,
    log_level=args.log_level,
    quiet=args.quiet,
    bvmon=args.bvmon,
    bvmon_word_size=args.bvmon_word_size,
    bvmon_trace_len=args.bvmon_trace_len
)

sys.exit(return_code.value)
