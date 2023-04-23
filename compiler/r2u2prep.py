import os
import shutil
import argparse
import sys

from c2po.c2po import compile

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+"/"

parser = argparse.ArgumentParser()
parser.add_argument("mltl",
                    help="file where mltl formula are stored or literal mltl formula")
parser.add_argument("sigs",
                    help="csv or sig file where variable names are mapped to memory locations")
parser.add_argument("-q","--quiet", action="store_true",
                    help="enable to disable output")
parser.add_argument("--config-file", default=__AbsolutePath__+"r2u2.conf",
                    help="path to configuration file")
parser.add_argument("--header-file",
                    default=__AbsolutePath__+"gen_files/config_files/R2U2Config.h",
                    help="path to configuration header file, uses this file to detect if recompilation is needed")
parser.add_argument("--output-file", default=__AbsolutePath__+"r2u2_spec.bin",
                    help="location where output file will be generated")
parser.add_argument("--compiler-dir", default=__AbsolutePath__+"Compiler/",
                    help="location where compiler programs will be called from")
parser.add_argument("--assembler-dir",default=__AbsolutePath__+"Assembler/",
                    help="location where assembly and configuration programs will be called from")
parser.add_argument("--int-width", default=8,
                    help="bit width for integer types")
parser.add_argument("--int-signed", action="store_true",
                    help="set int types to signed")
parser.add_argument("--float-width", default=32,
                    help="bit width for floating point types")
parser.add_argument("--no-binaries", action="store_true",
                    help="generate config.c file in place of binaries")
parser.add_argument("--booleanizer", action="store_true",
                    help="enable booleanizer")
parser.add_argument("--extops", action="store_true",
                    help="enable extended operations")
parser.add_argument("--rewrite", action="store_true",
                    help="enable MLTL rewrite rule optimizations")
parser.add_argument("--atomic-checker", action="store_true",
                    help="enable atomic checkers")
parser.add_argument("--no-color", action="store_false",
                    help="disable color in logging")
args = parser.parse_args()

# If the argument is a valid file,
return_code = 0
if(os.path.isfile(args.mltl)):
    mltl = open(args.mltl,"r").read()
    if(os.path.isfile(args.sigs)):
        return_code = compile(args.mltl, args.sigs, output_filename=args.output_file, int_width=args.int_width, int_signed=args.int_signed, float_width=args.float_width, at=args.atomic_checker, bz=args.booleanizer, cse=True, extops=args.extops, rewrite=args.rewrite, color=args.no_color, quiet=args.quiet)
    else:
        print(f"Signal mapping argument '{args.sigs}' not a valid file")
        return_code = 1
else:
    print(f"MLTL file \"{args.sigs}\" not a valid file")
    return_code = 1

sys.exit(return_code)
