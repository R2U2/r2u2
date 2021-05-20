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

#from AT import *

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

    FT = {}
    PT = {}
    AT = []

    # Strip out any null (\n) characters from the MLTL string ???
    #MLTL = MLTL.replace('\n','') ???

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
            print('************************************************************')
            print('Formula has both past-time and future-time operators.')
            print('R2U2 does not support mixed-time formulas.')
            print('The following formula is invalid: ' + line)
        # Else, if a formula is just past-time,
        elif((isPT > 0) and (isFT == 0)):
            # Put it in the PT list, for the PT call of postgraph
            PT.update({form_num: line + ';\n'})
        # Else, if the formula is future-time or just propositional logic,
        elif((isPT == 0) and (isFT >= 0) and (isAtom == 0)):
            # Put it in the FT list, for the FT call of postgraph
            FT.update({form_num: line + ';\n'})
        # Else if the formula is an atomic assignment
        elif(isAtom > 0):
            # Only add atomics to the set
            AT.append(line + ';')

    AT_str = ""
    for line in AT:
        if(re.fullmatch('\s*', line)):
            continue
        AT_str += line

    # Call Postgraph for both sets of formulas, Past-Time (PT) and Future-Time (FT)
    if(len(FT) != 0):
        print('************************** FT ASM **************************')
        FT_str = ""
        for i in range(max(FT.keys())+1):
            if i in FT:
                FT_str += FT[i]
            else:
                FT_str += "\n"
        #print(FT_str)
        subprocess.run(['python3',  args.compiler_dir+'main.py', FT_str, 'ft',
                        AT_str, binary_dir])
    if(len(PT) != 0):
        print('************************** PT ASM **************************')
        PT_str = ""
        for i in range(max(PT.keys())+1):
            if i in PT:
                PT_str += PT[i]
            else:
                PT_str += "\n"
        subprocess.run(['python3', args.compiler_dir+'main.py', PT_str, 'pt',
                        AT_str, binary_dir])
    # Compile AT instructions
    if(len(AT) != 0):
        print('************************** AT ASM **************************')
        subprocess.run(['python3', args.compiler_dir+'main.py', '', 'at',
                        AT_str, binary_dir])

    # Check to see if ft.asm exists
    if(not os.path.isfile(binary_dir+'ft.asm')):
        # If it doesn't, make a blank assembly that is just an end sequence
        f = open(binary_dir+'ft.asm','w+')
        f.write('s0: end sequence')
        f.close()
    if(not os.path.isfile(binary_dir+'ftscq.asm')):
        f = open(__BinFileDir__+'ftscq.asm', 'w+')
        f.write('0 0')
        f.close()
    # Check to see if pt.asm exists
    if(not os.path.isfile(binary_dir+'pt.asm')):
        # If it doesn't, make a blank assembly that is just an end sequence
        f = open(binary_dir+'pt.asm','w+')
        f.write('s0: end sequence')
        f.close()
    # Check to see if at.asm exists
    if(not os.path.isfile(binary_dir+'at.asm')):
        # If it doesn't, make a blank assembly
        f = open(binary_dir+'at.asm','w+')
        f.write(' ')
        f.close()

    if not os.path.isdir(args.output_dir+'config_files/'):
        os.mkdir(args.output_dir+'config_files/')

    subprocess.run(['python3', args.assembler_dir+'main.py',
                    args.config_file,
                    args.header_file,
                    args.output_dir+'config_files/R2U2Config.h',
                    binary_dir+'pt.asm',
                    binary_dir+'ft.asm',
                    binary_dir+'ftscq.asm',
                    binary_dir+'at.asm',
                    str(TIMESTAMP_WIDTH),
                    args.output_dir,
                    str(args.no_binaries)])
    print('************************************************************')
    print('Output files are located in the '+args.output_dir+' directory')
    print('Use '+args.output_dir+'binary_files/ as input to r2u2')
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
    args = parser.parse_args()
    main(args)
