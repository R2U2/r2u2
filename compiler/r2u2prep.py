from ast import arg
import os
import shutil
import argparse
import sys

from c2po.main import compile

parser = argparse.ArgumentParser()
parser.add_argument("mltl",
                    help="file where mltl formula are stored")
parser.add_argument("sigs",
                    help="csv or map file where variable names are mapped to memory locations")
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
parser.add_argument("--booleanizer", action="store_true",
                    help="enable booleanizer")
parser.add_argument("--cse", action="store_true",
                    help="enable CSE optimization")
parser.add_argument("--extops", action="store_true",
                    help="enable extended operations")
parser.add_argument("--rewrite", action="store_true",
                    help="enable MLTL rewrite rule optimizations")
parser.add_argument("--atomic-checker", action="store_true",
                    help="enable atomic checkers")
parser.add_argument("--disable-color", action="store_false",
                    help="disable color in logging")
parser.add_argument("--disable-assemble", action="store_false",
                    help="disable assembly generation")
args = parser.parse_args()

# If the argument is a valid file,
return_code = 0
if(os.path.isfile(args.mltl)):
    mltl = open(args.mltl,"r").read()
    if(os.path.isfile(args.sigs)):
        return_code = compile(args.mltl, args.sigs, impl=args.implementation, enable_assemble=(not args.disable_assemble), output_filename=args.output_file, int_width=args.int_width, int_signed=args.int_signed, float_width=args.float_width, enable_at=args.atomic_checker, enable_bz=args.booleanizer, enable_cse=args.cse, enable_extops=args.extops, enable_rewrite=args.rewrite, enable_color=args.disable_color, quiet=args.quiet)
    else:
        print(f"Signal mapping argument '{args.sigs}' not a valid file")
        return_code = 1
else:
    print(f"MLTL file \"{args.sigs}\" not a valid file")
    return_code = 1

sys.exit(return_code)
