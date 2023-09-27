import os
import argparse
import sys

from c2po.main import compile

parser = argparse.ArgumentParser()
parser.add_argument("mltl",
                    help="file where mltl formula are stored")
parser.add_argument("--trace-file",
                    help="csv file where variable names are mapped to memory locations using file header")
parser.add_argument("--map-file",
                    help="map file where variable names are mapped to memory locations")
parser.add_argument("-q","--quiet", action="store_true",
                    help="disable output")
parser.add_argument("--implementation", default="c",
                    help="target R2U2 implementation version (one of 'c', 'c++', 'vhdl')")
parser.add_argument("--output-file", default="r2u2_spec.bin",
                    help="location where output file will be generated")
parser.add_argument("--int-width", default=8,
                    help="bit width for integer types")
parser.add_argument("--int-signed", action="store_true",
                    help="set int types to signed")
parser.add_argument("--float-width", default=32,
                    help="bit width for floating point types")
parser.add_argument("--atomic-checker", action="store_true",
                    help="enable atomic checkers")
parser.add_argument("--booleanizer", action="store_true",
                    help="enable booleanizer")
parser.add_argument("--disable-cse", action="store_false",
                    help="disable CSE optimization")
parser.add_argument("--extops", action="store_true",
                    help="enable extended operations")
parser.add_argument("--disable-rewrite", action="store_false",
                    help="disable MLTL rewrite rule optimizations")
parser.add_argument("--disable-assemble", action="store_false",
                    help="disable assembly generation")
parser.add_argument("--mission-time", default=-1, type=int,
                    help="define mission time (overriding any inference from a simulated input trace)")
args = parser.parse_args()

return_code = compile(args.mltl, trace_filename=args.trace_file, map_filename=args.map_file, impl=args.implementation, enable_assemble=args.disable_assemble, output_filename=args.output_file, int_width=args.int_width, int_signed=args.int_signed, float_width=args.float_width, enable_at=args.atomic_checker, enable_bz=args.booleanizer, enable_cse=args.disable_cse, enable_extops=args.extops, enable_rewrite=args.disable_rewrite, quiet=args.quiet, mission_time=args.mission_time)

sys.exit(return_code)
