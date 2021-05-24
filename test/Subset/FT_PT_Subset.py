#------------------------------------------------------------------------------------#
# Author:      Pei Zhang(1st), Matt Cauwels(2nd)
# Date:        November 10th, 2020
# File Name:   FT_PT_Subset.py
# Description: A Python 3 script used to automatically run a collection of
#              future-time, past-time, and propositional logic formulas to test all
#              available operators are funcitoning properly.
#------------------------------------------------------------------------------------#
import shutil
import os
import argparse
import subprocess
import re
from subprocess import check_output

'''
Paths needed to navigate across the r2u2 directory
'''
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__TLDir__        = __AbsolutePath__+'../TL_formula/formulaSubset/'
__InputDir__     = __AbsolutePath__+'../Inputs/inputFiles/'
__CDir__         = __AbsolutePath__+'../../R2U2_C/'
__ResultDIR__    = __AbsolutePath__+'../results/'
__testDir__     = __AbsolutePath__+'../'
__toolsDir__     = __AbsolutePath__+'../../tools/'
__CompilerDir__  = __toolsDir__+'Compiler/'
__BinDir__       = __toolsDir__+'gen_files/binary_files/'


# Names of the directories where the results for each version are stored
__ResultCDir__   = 'c_version/'
'''

'''
def parserInfo():
    parser = argparse.ArgumentParser(description='Suffer from R2U2 Runtime Verification Regression Test')
    parser.add_argument('-v','--version', help='Choose the R2U2 implementation version to test', required=False)
    parser.add_argument('-r','--remove', help='Remove all R2U2 log files from the /results/ directory', required=False)
    args = vars(parser.parse_args())
    return args

'''
Method for listing all the files within a given directory.
'''
def list_file():
    from os import listdir
    from os.path import isfile, join
    formulaFiles,inputFiles = [[f for f in listdir(i) if isfile(join(i, f))] for i in (__TLDir__,__InputDir__)]
    formulaFiles = sorted(formulaFiles)
    inputFiles = sorted(inputFiles)
    return formulaFiles,inputFiles

'''
Method for testing the C version of R2U2.
Note: You must 'make' the R2U2 file within the R2U2_C/ directory prior to running this method!
'''
def test_c(formulaFiles,inputFiles):
    __OutputDIR__ = __ResultDIR__+__ResultCDir__
    _input = 'input0053.csv'
    if not os.path.exists(__OutputDIR__):
        os.makedirs(__OutputDIR__)
    # For all formula files within the formulaFiles directory
    for _formulaFile in formulaFiles:
        formula = open(__TLDir__+_formulaFile,'r').read()
        subprocess.run(['python3', __toolsDir__+'r2u2prep.py',formula],stdout=subprocess.PIPE)
        form   = _formulaFile.replace('.mltl','')
        trace  = _input.replace('.csv','')
        filename = __OutputDIR__+form+'_'+trace+'.txt'
        subprocess.run([__CDir__+'bin/r2u2',__BinDir__,__InputDir__+_input],stdout=subprocess.PIPE)
        subprocess.run(['mv','R2U2.log',filename],stdout=subprocess.PIPE)
    # For the last run, which should be a concatenation of all the formulas, copy the name
    # back to R2U2.log
    subprocess.run(['mv',filename,__OutputDIR__+'R2U2.log'],stdout=subprocess.PIPE)
    # Split the multi-formula run into individual files.
    subprocess.run([__toolsDir__+'split_verdicts.sh',__OutputDIR__+'R2U2.log'],stdout=subprocess.PIPE)
    # Move all the newly split files to the results directory.
    for i in range(0,12):
        filename = __testDir__+'R2U2_formula'+str(i)+'.txt'
        subprocess.run(['mv',filename,__OutputDIR__+'R2U2_formula'+str(i)+'.txt'],stdout=subprocess.PIPE)
    # Remove the overall R2U2.log file from the results directory
    subprocess.run(['rm',__OutputDIR__+'R2U2.log'])
'''
The main method for this file.
    - Parses the directories for the input traces and the formula files.
    - Parses the input arguement, to determine if you are running a test or cleaning the directories.
    - If running the test,determines which version of R2U2 you want to test.
'''
def main():
    args = parserInfo()
    # If there is the remove flag, remove all directories and files in the results directory
    if(args['remove']):
        print('Removing all R2U2 log files from the results directory')
        shutil.rmtree(__ResultDIR__+__ResultCDir__, ignore_errors=True)

   # If not, then test the specified version of R2U2
    elif(args['version']):
        formulaFiles,inputFiles = list_file()
        test_c(formulaFiles,inputFiles)
    # Else, throw an error message
    else:
        print('ERROR: Invalid arguement flags or missing input arguement after flag')
        print('Use "-h" flag for more information')

if __name__ == "__main__":
   main()
