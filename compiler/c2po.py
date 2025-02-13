import argparse
import sys

import c2po.main
import c2po.options

parser = argparse.ArgumentParser()
parser.add_argument("spec",
                    help="specification file (either .c2po or .mltl)")

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
                    help="enable stat output")

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
parser.add_argument("-da", "--disable-aux", action="store_false",
                    help = "disable aux data (e.g., contract status and specification naming)")

parser.add_argument("-dc", "--disable-cse", action="store_false",
                    help="disable CSE optimization")
parser.add_argument("-dr", "--disable-rewrite", action="store_false",
                    help="disable MLTL rewrite rule optimizations")
parser.add_argument("--extops", action="store_true",
                    help="enable extended operations")

parser.add_argument("-nnf", action="store_true",
                    help="enable negation normal form")
parser.add_argument("-bnf", action="store_true",
                    help="enable boolean normal form")

parser.add_argument("-eq", "--eqsat", action="store_true",
                    help="enable equality saturation")
parser.add_argument("-sat", "--check-sat", action="store_true",
                    help="enable satisfiability checking of future-time formulas")

parser.add_argument("--timeout-eqsat", type=int, default=3600, 
                    help="set the timeout of equality saturation calls in seconds (default: 3600)")
parser.add_argument("--timeout-sat", type=int, default=3600, 
                    help="set the timeout of sat calls in seconds (default: 3600)")

parser.add_argument("--write-c2po", nargs="?", const=c2po.options.EMPTY_FILENAME,
                    help="write final program in C2PO input format")
parser.add_argument("--write-mltl", nargs="?", const=c2po.options.EMPTY_FILENAME,
                    help="write final program in MLTL standard format")
parser.add_argument("--write-prefix", nargs="?", const=c2po.options.EMPTY_FILENAME,
                    help="write final program in prefix notation")
parser.add_argument("--write-pickle", nargs="?", const=c2po.options.EMPTY_FILENAME,
                    help="pickle the final program")
parser.add_argument("--write-smt", nargs="?", const=c2po.options.EMPTY_FILENAME,
                    help="write SMT encoding of FT formulas")

parser.add_argument("--copyback",
                    help="name of directory to copy workdir contents to upon termination")

parser.add_argument("-fo", "--first-order", action="store_true",
                    help="enable first-order mode")
parser.add_argument("--first-order-bounds",
                    help="file storing bounds for first-order formula quantifier guards")
parser.add_argument("--first-order-trace",
                    help="first-order trace file")

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
    enable_aux=args.disable_aux,
    enable_cse=args.disable_cse, 
    enable_extops=args.extops, 
    enable_rewrite=args.disable_rewrite, 
    enable_eqsat=args.eqsat,
    enable_nnf=args.nnf,
    enable_bnf=args.bnf,
    enable_sat=args.check_sat,
    write_c2po_filename=args.write_c2po,
    write_mltl_filename=args.write_mltl,
    write_prefix_filename=args.write_prefix,
    write_pickle_filename=args.write_pickle,
    write_smt_dirname=args.write_smt,
    timeout_eqsat=args.timeout_eqsat,
    timeout_sat=args.timeout_sat,
    copyback_dirname=args.copyback,
    enable_first_order=args.first_order,
    fo_bounds_filename=args.first_order_bounds,
    fo_trace_filename=args.first_order_trace,
    stats=args.stats,
    debug=args.debug,
    log_level=args.log_level,
    quiet=args.quiet
)

sys.exit(return_code.value)
