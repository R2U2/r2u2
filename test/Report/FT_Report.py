#------------------------------------------------------------------------------------#
# Programmer: Matt Cauwels
# Date: November 10th, 2020
# Project: R2U2 - Regression Testing
# File Name: FT_Report.py
# Description: Scan through the results files of R2U2 and compare them against one 
#              another. Report if any result mismatches against its oracle. Write the 
#              results in a FT_Results.txt file
#------------------------------------------------------------------------------------#
import subprocess
import os
from os import listdir
from os.path import isfile, join

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__OracleDir__    = __AbsolutePath__+'../Oracle/FT_Oracle/'
__ResultCDir__   = __AbsolutePath__+'../results/c_version/'

# Create the Results.txt
f = open("FT_Results.txt",'w')

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

# Now read the results file and print which formulas have diffs
f = open("FT_Results.txt",'r').read()

lines = f.split('\n')
ResultsArray = []
i = -1
for line in lines:
    # Ignoring blank lines,
    if(line != ''):
        # If the line starts with a comment,
        if(line[0] == '#'):
            # Pull out the file's name from the comment
            f = line.split(' ')[3]
            # Add a new list to the list
            ResultsArray.append([])
            # Update the Results Array's index
            i = len(ResultsArray) - 1
            # Append the filename to the ResultsArray[i]
            ResultsArray[i].append(f)
            # Initialize the ResultsArray's error count to zero
            ResultsArray[i].append(0)
        # If the line doesn't start with a comment,
        else:
            # Then 
            ResultsArray[i][1] = ResultsArray[i][1] + 1

differences = False
for i in range(0,len(ResultsArray)):
    if(ResultsArray[i][1] > 0):
        print('Differences between Oracle and R2U2 for ' + ResultsArray[i][0])

if differences == True:
    raise(RuntimeError("Differences found in FT Report"))
