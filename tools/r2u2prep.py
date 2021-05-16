#!/usr/bin/python3
#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 29th, 2020
# File Name:   r2u2prep.py
# Description: 
#------------------------------------------------------------------------------------#
import sys
import os
import subprocess
import shutil
import re
import Compiler.MLTL_Compiler

TIMESTAMP_WIDTH = 4
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__CompilerDir__  = __AbsolutePath__     + 'Compiler/'
__BinGenDir__    = __AbsolutePath__     + 'AssemblyToBinary/'
__BinFileDir__   = __AbsolutePath__     + 'binary_files/'

def main():

    # Remove 'binary_files' directory, if it exists, and start fresh
    if(os.path.isdir(__BinFileDir__)):
        shutil.rmtree(__BinFileDir__)

    # If the arguement is a valid file,
    if(os.path.isfile(__AbsolutePath__ + sys.argv[1])):
        MLTL = open(sys.argv[1],'r').read()
    else:
        MLTL = sys.argv[1]
    FT = {}
    PT = {}
    
    # Strip out any null (\n) characters from the MLTL string
    MLTL = MLTL.replace('\n','')
    
    # Split the PT and FT
    for form_num, line in enumerate(MLTL.split(';')):
        line = line.strip('\n ')
        if re.match('^.*#', line):
            line = re.match('^.*#', line).group()[:-1]
        # Ignore lines that are blank
        if(re.fullmatch('\s*', line)):
            continue
        # Iterate through the line and determine if it is FT or PT
        isFT = 0
        isPT = 0
        for p in line:
            # Determine if the line contains a FT oeprator
            if((p == 'G') or (p == 'F') or (p == 'U') or (p == 'R')):
                isFT = isFT + 1
            # Determine if the line contrains a PT operator
            elif((p == 'Y') or (p == 'H') or (p == 'O') or (p == 'S')):
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
        elif((isPT == 0) and (isFT >= 0)):
            # Put it in the FT list, for the FT call of postgraph
            FT.update({form_num: line + ';\n'})

    # Call Postgraph for both sets of formulas, Past-Time (PT) and Future-Time (FT)
    if(len(FT) != 0):
        print('************************** FT ASM **************************')
        FT_str = ""
        for i in range(max(FT.keys())+1):
            if i in FT:
                FT_str += FT[i]
            else:
                FT_str += "\n"
        subprocess.run(['python3', __CompilerDir__+'main.py', FT_str, 'ft'])
        # MLTL = FT_str
        # FTorPT = 'ft'
        # postgraph = Compiler.MLTL_Compiler.Postgraph(MLTL, FTorPT, optimize_cse=True)
        # del postgraph
    if(len(PT) != 0):
        print('************************** PT ASM **************************')
        PT_str = ""
        for i in range(max(PT.keys())+1):
            if i in PT:
                PT_str += PT[i]
            else:
                PT_str += "\n"
        subprocess.run(['python3', __CompilerDir__+'main.py', PT_str, 'pt'])
        # MLTL = PT_str
        # FTorPT = 'pt'
        # postgraph = Compiler.MLTL_Compiler.Postgraph(MLTL, FTorPT, optimize_cse=True)
        # del postgraph

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
    subprocess.run(['python3', __BinGenDir__+'ftas.py', __BinFileDir__+'ft.asm', str(TIMESTAMP_WIDTH)])
    # Check to see if pt.asm exists
    if(not os.path.isfile(__BinFileDir__+'pt.asm')):
        # If it doesn't, make a blank assembly that is just an end sequence
        f = open(__BinFileDir__+'pt.asm','w+')
        f.write('s0: end sequence')
        f.close()
    print('************************************************************')
    subprocess.run(['python3', __BinGenDir__+'ptas.py', __BinFileDir__+'pt.asm',str( TIMESTAMP_WIDTH)])

    print('************************************************************')
    print('Binary files are located in the '+__BinFileDir__+' directory')
    print('************************************************************')
    
    #'reset' MLTLCompiler by deleting from memory and reimporting
    del Compiler.MLTL_Compiler

if __name__ == "__main__":
    main()
