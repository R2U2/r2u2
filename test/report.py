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
f.close()
# Loop for each formula
for formulaNum in range(FORMULA_LIMIT):
    # Format the formula filename
    if(formulaNum < 10):
        formulaFilename = "test000" + str(formulaNum)
    else:
        formulaFilename = "test00"  + str(formulaNum)
    #try:
    if(True):
        # Loop for each input
        for inputNum in range(INPUT_LIMIT):
            # Format the input filename
            if(inputNum < 10):
                inputFilename = "input000" + str(inputNum)
            else:
                inputFilename = "input00"  + str(inputNum)
            result = "results/c_version/"+formulaFilename+"_"+inputFilename+".txt"
            oracle = "Oracle/oracleFiles/"+formulaFilename+"_"+inputFilename
            f = open("Results.txt",'a+')
            f.write("# Diff output " + result + ' and ' + oracle + '\n')
            f.close()
            f = open("Results.txt",'a+')
            subprocess.run(['diff',result,oracle],stdout=f)
            f.close()
            '''
            exitFlag = False
            
            # Open each versions file and loop through the lines to see if they're equivalent
            f1 = open("results/c_version/"+formulaFilename+"_"+inputFilename+'.txt', 'r')
            f2 = open("Oracle/oracleFiles/"+formulaFilename+"_"+inputFilename, 'r')
            for line1 in f1:
                for line2 in f2:
                    lineNum = lineNum + 1
                    if line1 != line2:
                        line = "Mismatch between Oracle and R2U2-C output for Formula " + str(formulaNum) + " and Input trace " + str(inputNum) + " on line " + str(lineNum)
                        print(line)
                        f.write(line + "\n");
                        exitFlag = True
                        break
                if(exitFlag):
                    break
            f1.close();
            f2.close();
            lineNum = 0;
            '''
    #except:
    #    print('Missing formula '+str(formulaNum)+' at input '+str(inputNum))
    #    pass
            
f.close();