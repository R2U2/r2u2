#!/usr/bin/python3
#------------------------------------------------------------------------------#
# Author:      Matt Cauwels
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
__CompilerDir__  = __AbsolutePath__     + 'Compiler/'
__BinGenDir__    = __AbsolutePath__     + 'AssemblyToBinary/'
__BinFileDir__   = __AbsolutePath__     + 'binary_files/'

def main(mltl, config):

    # Remove 'binary_files' directory, if it exists, and start fresh
    if(os.path.isdir(__BinFileDir__)):
        shutil.rmtree(__BinFileDir__)

    # If the arguement is a valid file,
    if(os.path.isfile(__AbsolutePath__ + mltl)):
        MLTL = open(mltl,'r').read()
    elif(os.path.isfile(mltl)):
        MLTL = open(mltl,'r').read()
    else:
        MLTL = mltl

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
        subprocess.run(['python3', __CompilerDir__+'main.py', FT_str, 'ft', AT_str])
    if(len(PT) != 0):
        print('************************** PT ASM **************************')
        PT_str = ""
        for i in range(max(PT.keys())+1):
            if i in PT:
                PT_str += PT[i]
            else:
                PT_str += "\n"
        subprocess.run(['python3', __CompilerDir__+'main.py', PT_str, 'pt', AT_str])
    # Compile AT instructions
    if(len(AT) != 0):
        print('************************************************************')
        subprocess.run(['python3', __CompilerDir__+'main.py', '', 'at', AT_str])

    # Check to see if ft.asm exists
    if(not os.path.isfile(__BinFileDir__+'ft.asm')):
        # If it doesn't, make a blank assembly that is just an end sequence
        f = open(__BinFileDir__+'ft.asm','w+')
        f.write('s0: end sequence')
        f.close()
        f = open(__BinFileDir__+'ftscq.bin', 'w+')
        f.write(' 00000000000000000000000000000011')
        f.close
    print('************************************************************')
    subprocess.run(['python3', __BinGenDir__+'ftas.py', __BinFileDir__+'ft.asm',
                    __BinFileDir__+'ftscq.asm', str(TIMESTAMP_WIDTH), str(config)])
    # Check to see if pt.asm exists
    if(not os.path.isfile(__BinFileDir__+'pt.asm')):
        # If it doesn't, make a blank assembly that is just an end sequence
        f = open(__BinFileDir__+'pt.asm','w+')
        f.write('s0: end sequence')
        f.close()
    print('************************************************************')
    subprocess.run(['python3', __BinGenDir__+'ptas.py', __BinFileDir__+'pt.asm',
                    str( TIMESTAMP_WIDTH), str(config)])
    print('************************************************************')
    # Check to see if ft.asm exists
    if(not os.path.isfile(__BinFileDir__+'at.asm')):
        # If it doesn't, make a blank assembly
        f = open(__BinFileDir__+'at.asm','w+')
        f.write(' ')
        f.close()
    subprocess.run(['python3', __BinGenDir__+'atas.py', __BinFileDir__+'at.asm',
                    str(config)])

    print('************************************************************')
    print('Generated files are located in the '+__BinFileDir__+' directory')
    if config:
        print('Move binary_files/config.c to src/binParser directory')
    print('************************************************************')

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("mltl", help="filename where mltl formula are stored or literal mltl formula")
    parser.add_argument("-c", "--config", help="generate config.c file in place of binaries",
                        action="store_true")
    args = parser.parse_args()
    main(args.mltl, args.config)
