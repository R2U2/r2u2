#------------------------------------------------------------------------------------#
# Programmer: Matt Cauwels
# Date: April 28th, 2020
# Project: R2U2 - Regression Testing
# File Name: results.py
# Description: Scan through the results files for all versions of R2U2 and
#              compare them against one another. Report if any version 
#              mismatches against the other two. Write the results in a 
#              Report.txt file
#------------------------------------------------------------------------------------#
import subprocess
import os
from os import listdir
from os.path import isfile, join

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__OracleDir__    = __AbsolutePath__+'Oracle/oracleHydra/'
__ResultCDir__   = __AbsolutePath__+'results/c_version/'

# Create the Results.txt
f = open("HydraResults.txt",'w')

# Read in all the results and oracle files
oracleFiles,resultsFiles = [[f for f in listdir(i) if isfile(join(i, f))] for i in (__OracleDir__,__ResultCDir__)]

# Loop for each formula
for _oracle in oracleFiles:
    # Loop for each input
    for _result in resultsFiles:
        if(_oracle == _result):
            # Format the diff file
            f.write("# Diff output " + _result + ' and ' + _oracle + '\n')
            f.flush()
            subprocess.run(['diff',__ResultCDir__+_result,__OracleDir__+_oracle],stdout=f)
            f.flush()
f.close();