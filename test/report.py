#------------------------------------------------------------------------------------#
# Programmer: Matt Cauwels
# Date: July 18th, 2019
# Project: R2U2 - Regression Testing
# File Name: results.py
# Description: Scan through the results files for all versions of R2U2 and
#              compare them against one another. Report if any version 
#              mismatches against the other two. Write the results in a 
#              Report.txt file
#------------------------------------------------------------------------------------#
import subprocess

# The maximum number of Inputs and Formulas
INPUT_LIMIT = 53
FORMULA_LIMIT = 33

# Initialize the Formula and Input iterators
inputNum   = 0
formulaNum = 0
lineNum    = 0
# Create the Results.txt
f = open("Results.txt",'w')

# Loop for each formula
for formulaNum in range(FORMULA_LIMIT):
    # Format the formula filename
    if(formulaNum < 10):
        formulaFilename = "test000" + str(formulaNum)
    else:
        formulaFilename = "test00"  + str(formulaNum)
    # Loop for each input
    for inputNum in range(INPUT_LIMIT):
        # Format the input filename
        if(inputNum < 10):
            inputFilename = "input000" + str(inputNum)
        else:
            inputFilename = "input00"  + str(inputNum)
        result = "results/c_version/"+formulaFilename+"_"+inputFilename+".txt"
        oracle = "Oracle/oracleFiles/"+formulaFilename+"_"+inputFilename+".txt"
        f.write("# Diff output " + result + ' and ' + oracle + '\n')
        f.flush()
        subprocess.run(['diff',result,oracle],stdout=f)
        f.flush()
            
f.close();