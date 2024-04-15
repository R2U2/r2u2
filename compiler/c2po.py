import argparse
import sys

import c2po.main

parser = argparse.ArgumentParser()
parser.add_argument("mltl",
                    help="file where mltl formula are stored")

parser.add_argument("--trace", default="",
                    help="CSV file where variable names are mapped to signal order using file header")
parser.add_argument("--map", default="",
                    help="map file where variable names are mapped to signal order")

parser.add_argument("-q","--quiet", action="store_true",
                    help="disable output")
parser.add_argument("--debug", nargs="?", default=0, const=1, type=int,
                    help="set debug level (0=none, 1=basic, 2=extra)")
parser.add_argument("--stats", action="store_true",
                    help="enable stat output")

parser.add_argument("--impl", default="c", choices=["c","cpp","vhdl"],
                    help="specifies target R2U2 implementation version (default: c)")
parser.add_argument("-o", "--output", default="spec.bin",
                    help="specifies location where specification binary will be written")

parser.add_argument("--int-width", default=32, type=int,
                    help="specifies bit width for integer types (default: 32)")
parser.add_argument("--int-signed", action="store_true",
                    help="specifies signedness of int types (default: true)")
parser.add_argument("--float-width", default=32,
                    help="specifies bit width for floating point types (default: 32)")
parser.add_argument("--mission-time", type=int,
                    help="specifies mission time, overriding inference from a trace file, if present")
parser.add_argument("--endian", choices=c2po.main.BYTE_ORDER_SIGILS.keys(),
                    default=sys.byteorder, help=f"Specifies byte-order of spec file (default: {sys.byteorder})")

parser.add_argument("-at", "--atomic-checkers", action="store_true",
                    help="enable atomic checkers")
parser.add_argument("-bz", "--booleanizer", action="store_true",
                    help="enable booleanizer")

parser.add_argument("-p", "--parse", action="store_true",
                    help="only run the parser")
parser.add_argument("-tc", "--type-check", action="store_true",
                    help="only run the parser and type checker")
parser.add_argument("-c", "--compile", action="store_true",
                    help="only run the parser, type checker, and passes")

parser.add_argument("-dc", "--disable-cse", action="store_false",
                    help="disable CSE optimization")
parser.add_argument("-dr", "--disable-rewrite", action="store_false",
                    help="disable MLTL rewrite rule optimizations")
parser.add_argument("-eq", "--eqsat", action="store_true",
                    help="enable equality saturation")
parser.add_argument("--extops", action="store_true",
                    help="enable extended operations")

parser.add_argument("-nnf", action="store_true",
                    help="enable negation normal form")
parser.add_argument("-bnf", action="store_true",
                    help="enable boolean normal form")

parser.add_argument("-sat", "--check-sat", action="store_true",
                    help="enable satisfiability checking of future-time formulas")

parser.add_argument("--timeout-egglog", type=int, default=3600, 
                    help="set the timeout of egglog calls in seconds (default: 3600)")
parser.add_argument("--timeout-sat", type=int, default=3600, 
                    help="set the timeout of sat calls in seconds (default: 3600)")

parser.add_argument("--write-c2po", nargs="?", default=".", const="",
                    help="write final program in C2PO input format")
parser.add_argument("--write-mltl", nargs="?", default=".", const="",
                    help="write final program in MLTL standard format") 
parser.add_argument("--write-prefix", nargs="?", default=".", const="",
                    help="write final program in prefix notation")
parser.add_argument("--write-pickle", nargs="?", default=".", const="",
                    help="pickle the final program")
parser.add_argument("--write-smt", nargs="?", default=".", const="",
                    help="write SMT SAT encoding of FT formulas")

parser.add_argument("--keep", action="store_true",
                    help="keep working directory")
parser.add_argument("--workdir", help="location to place temporary files")

args = parser.parse_args()

return_code = c2po.main.compile(
    args.mltl, 
    trace_filename=args.trace, 
    map_filename=args.map, 
    impl=args.impl, 
    custom_mission_time=args.mission_time,
    output_filename=args.output, 
    int_width=args.int_width, 
    int_signed=args.int_signed, 
    float_width=args.float_width, 
    endian=args.endian,
    only_parse=args.parse,
    only_type_check=args.type_check,
    only_compile=args.compile,
    enable_atomic_checkers=args.atomic_checkers, 
    enable_booleanizer=args.booleanizer, 
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
    write_smt_dir=args.write_smt,
    timeout_egglog=args.timeout_egglog,
    timeout_sat=args.timeout_sat,
    keep=args.keep,
    workdir=args.workdir,
    stats=args.stats,
    debug=args.debug,
    quiet=args.quiet, 
)

sys.exit(return_code.value)
