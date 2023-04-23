#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        November 10th, 2020
# File Name:   LargePtSubset.py
# Description: A Python 3 script used to automatically run just the tests for large
#              input past-time test subsetss
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
__TLDir__        = __AbsolutePath__+'../TL_formula/'
__InputDir__     = __AbsolutePath__+'../Inputs/'
__CDir__          = __AbsolutePath__+'../../monitors/static/'
__ResultDIR__    = __AbsolutePath__+'../results/'
__testDir__     = __AbsolutePath__+'../'
__toolsDir__     = __AbsolutePath__+'../../tools/'
__compilerDir__  = __AbsolutePath__+'../../compiler/'
__binPath__       = __compilerDir__+'r2u2_spec.bin'



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
Method for testing the C version of R2U2.
Note: You must 'make' the R2U2 file within the R2U2_C/ directory prior to running this method!
'''
def test_c():
    __OutputDIR__ = __ResultDIR__+__ResultCDir__
    signal_filename = __InputDir__+'LargeTestInput.csv'
    if not os.path.exists(__OutputDIR__):
        os.makedirs(__OutputDIR__)
    # For all formula files within the formulaFiles directory
    mltl_filename = __TLDir__+'LargePtFormula.mltl'
    # print(formula)
    # For each formula within
    res = subprocess.run(['python3', __compilerDir__+'r2u2prep.py','--atomic-checker',"--output-file",__binPath__,mltl_filename,signal_filename],stdout=subprocess.PIPE)#,stdout=subprocess.PIPE)
    print(f"{' '.join(res.args)}\n{open(res.args[5], 'r').read()}\n{res.stdout.decode()}")
    filename = 'LargePT'+'.txt'
    subprocess.run([__CDir__+'build/r2u2',__binPath__,signal_filename],stdout=subprocess.PIPE)#,stdout=subprocess.PIPE)
    subprocess.run(['mv','R2U2.log',__OutputDIR__+filename])
    # Split the multi-formula run into individual files.
    subprocess.run([__toolsDir__+'split_verdicts.sh',__OutputDIR__+filename],stdout=subprocess.PIPE)
    # Move all the newly split files to the results directory.
    for i in range(0,4):
        filename = __testDir__+'LargePT_formula'+str(i)+'.txt'
        subprocess.run(['mv',filename,__OutputDIR__+'LargePT_formula'+str(i)+'.txt'],stdout=subprocess.PIPE)
    # Remove the overall R2U2.log file from the results directory
    subprocess.run(['rm',__OutputDIR__+'LargePT.txt'],stdout=subprocess.PIPE)
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
        test_c()
    # Else, throw an error message
    else:
        print('ERROR: Invalid arguement flags or missing input arguement after flag')
        print('Use "-h" flag for more information')

if __name__ == "__main__":
   main()
