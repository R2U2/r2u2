#!/usr/bin/python3
#------------------------------------------------------------------------------#
# Author:      Matt Cauwels, Chris Johannsen
# Date:        April 29th, 2020
# File Name:   r2u2prep.py
# Description:
#------------------------------------------------------------------------------#
import sys
import os
import subprocess
import shutil
import re
import argparse

from Compiler import Compiler
from Assembler.config import parse_config, check_updates, gen_config
from Assembler.ptas import assemble_pt
from Assembler.ftas import assemble_ft
from Assembler.atas import assemble_at
from Assembler.filters import valid_filters

TIMESTAMP_WIDTH = 4
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'

def main(args):

    binary_dir = args.output_dir + 'binary_files/'

    if not os.path.isdir(args.output_dir):
        os.mkdir(args.output_dir)

    # Remove binary files directory, if it exists, and start fresh
    if os.path.isdir(binary_dir):
        shutil.rmtree(binary_dir)

    # If the argument is a valid file,
    #if(os.path.isfile(__AbsolutePath__ + mltl)):
    #    MLTL = open(args.mltl,'r').read()
    if(os.path.isfile(args.mltl)):
        MLTL = open(args.mltl,'r').read()
    else:
        MLTL = args.mltl

    mltl_compiler = Compiler.Compiler(binary_dir, MLTL, valid_filters())
    mltl_compiler.preprocess()

    print('************************** FT ASM **************************')

    mltl_compiler.compile_ft('ft.asm')

    print('************************** PT ASM **************************')

    mltl_compiler.compile_pt('pt.asm')

    print('************************** AT ASM **************************')

    mltl_compiler.compile_at('at.asm')

    print('************************************************************')

    if not mltl_compiler.status:
        print('Error in compilation of MLTL or AT')
        return

    mltl_compiler.gen_alias_file('alias.txt')

    if not os.path.isdir(args.output_dir+'config_files/'):
        os.mkdir(args.output_dir+'config_files/')

    print('Generating configuration files')
    parse_config(args.config_file)
    check_updates(args.header_file)
    gen_config(args.output_dir+'config_files/R2U2Config.h')

    print('************************************************************')

    assemble_ft(binary_dir+'ft.asm', binary_dir+'ftscq.asm',
                str(TIMESTAMP_WIDTH), args.output_dir,
                str(args.no_binaries))

    assemble_pt(binary_dir+'pt.asm', str(TIMESTAMP_WIDTH), args.output_dir,
                str(args.no_binaries))

    assemble_at(binary_dir+'at.asm', args.output_dir, str(args.no_binaries))


    print('************************************************************')
    print('Output files are located in the '+args.output_dir+' directory')
    print('Use '+args.output_dir+'binary_files/ as input to r2u2')
    print('************************************************************')

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("mltl",
                        help="file where mltl formula are stored or literal mltl formula")
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
    parser.add_argument("--no-symbolic-names", action="store_true",
                        help="restricts use of symbolic names for atomics and signals")
    args = parser.parse_args()
    main(args)
