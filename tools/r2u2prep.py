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

from Compiler import compiler
from Assembler.config import *
from Assembler.ptas import assemble_pt
from Assembler.ftas import assemble_ft
from Assembler.atas import assemble_at

TIMESTAMP_WIDTH = 4
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'

def main(args):

    output_dir    = __AbsolutePath__ + args.output_dir
    binary_dir    = __AbsolutePath__ + args.output_dir + 'binary_files/'
    compiler_dir  = __AbsolutePath__ + args.compiler_dir
    assembler_dir = __AbsolutePath__ + args.assembler_dir

    if not os.path.isdir(output_dir):
        os.mkdir(output_dir)

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

    FT = ""
    PT = ""
    AT = ""

    # Split the PT and FT
    for form_num, line in enumerate(MLTL.split(';')):
        line = line.strip('\n ')
        # Ignore lines that are blank
        if(re.fullmatch('\s*', line)):
            continue
        # Iterate through the line and determine if it is FT or PT or atomic
        isFT = 0
        isPT = 0
        isAtom = 0

        # Determine if the line is an atomic mapping
        if(re.search(':=', line)):
            isAtom = isAtom + 1
        # Determine if the line contains a FT operator
        elif(re.search('[GFUR]', line)):
            isFT = isFT + 1
        # Determine if the line contains a PT operator
        elif(re.search('[YHOS]', line)):
            isPT = isPT + 1

        # If a formula has both PT and FT, throw an error and exit the program
        if((isPT > 0) and (isFT > 0)):
            print('***********************************************************')
            print('Formula has both past-time and future-time operators.')
            print('R2U2 does not support mixed-time formulas.')
            print('The following formula is invalid: ' + line)
        # Else, if a formula is just past-time,
        elif((isPT > 0) and (isFT == 0)):
            # Put it in the PT list, for the PT call of postgraph
            PT += line + ';\n'
        # Else, if the formula is future-time or just propositional logic,
        elif((isPT == 0) and (isFT >= 0) and (isAtom == 0)):
            # Put it in the FT list, for the FT call of postgraph
            FT += line + ';\n'
        # Else if the formula is an atomic assignment
        elif(isAtom > 0):
            # Only add atomics to the set
            AT += line + ';\n'

    mltl_compiler = compiler.Compiler(FT,PT,AT,binary_dir)

    print('************************** FT ASM **************************')

    if not FT == '':
        mltl_compiler.mltl_compile(FT, 'ft.asm', 'alias.txt')
    else:
        f = open(binary_dir+'ft.asm','w+')
        f.write('s0: end sequence')
        f.close()
        print('s0: end sequence')

    print('************************** PT ASM **************************')

    if not PT == '':
        mltl_compiler.mltl_compile(PT, 'pt.asm', 'alias.txt')
    else:
        f = open(binary_dir+'pt.asm','w+')
        f.write('s0: end sequence')
        f.close()
        print('s0: end sequence')

    print('************************** AT ASM **************************')

    mltl_compiler.at_compile(AT, 'at.asm', 'alias.txt')

    print('************************************************************')

    if not mltl_compiler.status:
        print('Error in compilation of MLTL or AT')
        return

    if not os.path.isdir(output_dir+'config_files/'):
        os.mkdir(output_dir+'config_files/')

    print('Generating configuration files')
    parse_config(args.config_file)
    check_updates(args.header_file)
    gen_config(args.output_dir+'config_files/R2U2Config.h',
        mltl_compiler.ref_atomics, mltl_compiler.signals)

    print('************************************************************')

    assemble_ft(binary_dir+'ft.asm', binary_dir+'ftscq.asm',
                str(TIMESTAMP_WIDTH), args.output_dir,
                str(args.no_binaries))

    assemble_pt(binary_dir+'pt.asm', str(TIMESTAMP_WIDTH), args.output_dir,
                str(args.no_binaries))

    assemble_at(binary_dir+'at.asm', args.output_dir, str(args.no_binaries))


    print('************************************************************')
    print('Output files are located in the '+output_dir+' directory')
    print('Use '+output_dir+'binary_files/ as input to r2u2')
    print('************************************************************')

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("mltl",
                        help="file where mltl formula are stored or literal mltl formula")
    parser.add_argument("--config-file", default='r2u2.conf',
                        help="path to configuration file")
    parser.add_argument("--header-file",
                        default='gen_files/config_files/R2U2Config.h',
                        help="path to configuration header file, uses this file to detect if recompilation is needed")
    parser.add_argument("--output-dir", default='gen_files/',
                        help="location where files will be generated")
    parser.add_argument("--compiler-dir", default='Compiler/',
                        help="location where compiler programs will be called from")
    parser.add_argument("--assembler-dir", default='Assembler/',
                        help="location where assembly and configuration programs will be called from")
    parser.add_argument("--no-binaries", action="store_true",
                        help="generate config.c file in place of binaries")
    parser.add_argument("--no-symbolic-names", action="store_true",
                        help="restricts use of symbolic names for atomics and signals")
    args = parser.parse_args()
    main(args)
