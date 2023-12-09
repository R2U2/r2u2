import argparse
import sys

from c2po.main import compile

parser = argparse.ArgumentParser()
parser.add_argument("mltl",
                    help="file where mltl formula are stored")
parser.add_argument("--trace", default="",
                    help="csv file where variable names are mapped to memory locations using file header")
parser.add_argument("--map", default="",
                    help="map file where variable names are mapped to memory locations")
parser.add_argument("-q","--quiet", action="store_true",
                    help="disable output")
parser.add_argument("-d","--debug", action="store_true",
                    help="enable debug output")
parser.add_argument("--impl", default="c",
                    help="target R2U2 implementation version (one of 'c', 'c++', 'vhdl')")
parser.add_argument("--output", default="spec.bin",
                    help="location where output file will be generated")

parser.add_argument("--int-width", default=8,
                    help="bit width for integer types")
parser.add_argument("--int-signed", action="store_true",
                    help="set int types to signed")
parser.add_argument("--float-width", default=32,
                    help="bit width for floating point types")
parser.add_argument("--mission-time", default=-1, type=int,
                    help="define mission time (overriding inference from a trace file)")
parser.add_argument("--endian", choices=['native', 'network', 'big', 'little'],
                    default=sys.byteorder, help='Select byte-order of spec file')

parser.add_argument("--atomic-checkers", action="store_true",
                    help="enable atomic checkers")
parser.add_argument("--booleanizer", action="store_true",
                    help="enable booleanizer")

parser.add_argument("--disable-assemble", action="store_false",
                    help="disable assembly generation")
parser.add_argument("--disable-cse", action="store_false",
                    help="disable CSE optimization")
parser.add_argument("--extops", action="store_true",
                    help="enable extended operations")
parser.add_argument("--disable-rewrite", action="store_false",
                    help="disable MLTL rewrite rule optimizations")
                    
parser.add_argument("--dump-ast", nargs="?", default=".", const="",
                    help="dump AST in pickle format")
parser.add_argument("--dump-mltl", nargs="?", default=".", const="",
                    help="dump input file in MLTL standard format")

args = parser.parse_args()

return_code = compile(
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
    enable_atomic_checkers=args.atomic_checkers, 
    enable_booleanizer=args.booleanizer, 
    enable_cse=args.disable_cse, 
    enable_extops=args.extops, 
    enable_rewrite=args.disable_rewrite, 
    enable_assemble=args.disable_assemble, 
    dump_ast_filename=args.dump_ast,
    dump_mltl_std_filename=args.dump_mltl,
    debug=args.debug,
    quiet=args.quiet, 
)

sys.exit(return_code.value)
