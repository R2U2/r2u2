#!/usr/bin/python3
#------------------------------------------------------------------------------#
# Author:      Matt Cauwels, Chris Johannsen
# Date:        April 29th, 2020
# File Name:   r2u2prep.py
# Description:
#------------------------------------------------------------------------------#
import os
import shutil
import argparse
import sys

from compiler.compiler import compile

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'

parser = argparse.ArgumentParser()
parser.add_argument("mltl",
                    help="file where mltl formula are stored or literal mltl formula")
parser.add_argument("sigs",
                    help="csv or sig file where variable names are mapped to memory locations")
parser.add_argument("-q","--quiet", action="store_true",
                    help="enable to disable output")
parser.add_argument("--config-file", default=__AbsolutePath__+'r2u2.conf',
                    help="path to configuration file")
parser.add_argument("--header-file",
                    default=__AbsolutePath__+'gen_files/config_files/R2U2Config.h',
                    help="path to configuration header file, uses this file to detect if recompilation is needed")
parser.add_argument("--output-dir", default=__AbsolutePath__+'gen_files/',
                    help="location where files will be generated")
parser.add_argument("--compiler-dir", default=__AbsolutePath__+'Compiler/',
                    help="location where compiler programs will be called from")
parser.add_argument("--assembler-dir",default=__AbsolutePath__+'Assembler/',
                    help="location where assembly and configuration programs will be called from")
parser.add_argument("--no-binaries", action="store_true",
                    help="generate config.c file in place of binaries")
parser.add_argument("--booleanizer", action="store_true",
                    help="enable booleanizer")
parser.add_argument("--no-color", action="store_true",
                    help="enable color in logging")
args = parser.parse_args()

binary_dir = args.output_dir + '/binary_files/'

if not os.path.isdir(args.output_dir):
    os.mkdir(args.output_dir)

# Remove binary files directory, if it exists, and start fresh
if os.path.isdir(binary_dir):
    shutil.rmtree(binary_dir)

# If the argument is a valid file,
return_code = 0
if(os.path.isfile(args.mltl)):
    mltl = open(args.mltl,'r').read()
    if(os.path.isfile(args.sigs)):
        return_code = compile(mltl, args.sigs, args.output_dir, args.booleanizer, True, args.no_color, args.quiet)
    else:
        print(f'Signal mapping argument \'{args.sigs}\' not a valid file')
        return_code = 1
else:
    print(f'MLTL file \'{args.sigs}\' not a valid file')
    return_code = 1

sys.exit(return_code)