#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 10th, 2020
# File Name:   genOracle.py
# Description: 
#------------------------------------------------------------------------------------#

import sys
import os

# Paths to input and formula directories (from oracle directory)
inputDir     = '../Inputs/inputFiles/'
oracleDir  = 'oracleFiles/'

# Filenames for each file type
inputFilename   = "input00"

# Number of input files
NumInputs = 52
# Number of formula files
NumFormulas = 36

#------------------------------------------------------------------------------------#
# Based on the input arguements, read in the input file and return the trace as a 2D 
# array
#------------------------------------------------------------------------------------#
def readInput(inCount):
    # Format the count of the input file name with the correct number of 0s
    if(inCount < 10):
        Count = "0" + str(inCount)
    else:
        Count = str(inCount)
    
    # Open the input file and read the inputs
    f = open(inputDir+inputFilename+Count,'r').read()
    # Split the file object by rows
    lines = f.split('\n')
    
    # Create the Array list, which will store the inputs as a 2D list, where
    # the outer list corresponds to the atomics and the inner list corresponds to 
    # each atomic's the time-steps
    Array = []
    
    # Determine the number of columns in the input file
    for i in range(0,len(lines[0].split(','))):
        Array.append([])
    
    # Need a try statement or else there is an exception thrown when reading the 
    # end-of-file charater
    try:
        # Read each row
        for line in lines:
            # Split each row segment into columns
            part = line.split(',')
            # For all columns of that row,
            for i in range(0,len(part)):
                # Append the number to the corresponding list
                Array[i].append(float(part[i]))        
    # If an exception is raised when parsing the input file, ignore it
    except:
        pass
    
    # Return the Array list
    return(Array)

#------------------------------------------------------------------------------------#
# 
#------------------------------------------------------------------------------------#
def getVerdict(formNum, Input):
    Verdict = []
    # 0.) !a0
    if(formNum == 0):
        for i in range(0,len(Input[0])):
            Verdict.append(not Input[0][i])
        pcNum = 2
        formulaFilename = "test0000"
        
    # 1.) (a0 & a1)
    elif(formNum == 1):
        for i in range(0,len(Input[0])):
            Verdict.append(Input[0][i] and Input[1][i])
        pcNum = 3
        formulaFilename = "test0001"
        
    # 2.) G[0] (a0)
    elif(formNum == 2):
        for i in range(0,len(Input[0])):
            Verdict.append(Input[0][i])
        pcNum = 2
        formulaFilename = "test0002"
        
    # 3.) G[5] (a0)
    elif(formNum == 3):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[0][i] and Input[0][i+1] and Input[0][i+2] and Input[0][i+3]and Input[0][i+4] and Input[0][i+5])
            except:
                pass
        pcNum = 2
        formulaFilename = "test0003"
        
    # 4.) G[0,0] (a0)
    elif(formNum == 4):
        for i in range(0,len(Input[0])):
            Verdict.append(Input[0][i])
        pcNum = 2
        formulaFilename = "test0004"
        
    # 5.) G[0,1] (a0)
    elif(formNum == 5):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[0][i] and Input[0][i+1])
            except:
                pass
        pcNum = 2
        formulaFilename = "test0005"
        
    # 6.) G[5,10] (a0)
    elif(formNum == 6):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[0][i+5] and Input[0][i+6] and Input[0][i+7] and Input[0][i+8] and Input[0][i+9] and Input[0][i+10])
            except:
                pass
        pcNum = 2
        formulaFilename = "test0006"
        
    # 7.) (a0) U[0,0] (a1) *****
    elif(formNum == 7):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((not Input[0][i]) and Input[1][i])
            except:
                pass
        pcNum = 3
        formulaFilename = "test0007"
    
    # 8.) (a0) U[0,1] (a1) *****
    elif(formNum == 8):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and (not Input[1][i]) and (not Input[0][i+1]) and Input[1][i+1]) or ((not Input[0][i]) and Input[1][i] and (not Input[0][i+1]) and Input[1][i+1]))
            except:
                pass
        pcNum = 3
        formulaFilename = "test0008"
    
    # 9.) (a0) U[5,10] (a1) *****
    elif(formNum == 9):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+5]) and Input[1][i+5] and (not Input[0][i+6]) and Input[1][i+6] and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10])or (Input[0][i+5] and (not Input[1][i+5]) and (not Input[0][i+6]) and Input[1][i+6] and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and Input[0][i+8] and (not Input[1][i+8]) and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and Input[0][i+8] and (not Input[1][i+8]) and Input[0][i+9] and (not Input[1][i+9]) and (not Input[0][i+10]) and Input[1][i+10]))
            except:
                pass
        pcNum = 3
        formulaFilename = "test0009"
    
    # 10.) (a0) U[0,2] (a1) *****
    elif(formNum == 10):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i]) and Input[1][i] and (not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i] and (not Input[1][i]) and (not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i] and (not Input[1][i]) and Input[0][i+1] and (not Input[1][i+1]) and (not Input[0][i+2]) and Input[1][i+2]))
            except:
                pass
        pcNum = 3
        formulaFilename = "test0010"
    
    # 12.) (a0) U[1,2] (a1) *****
    elif(formNum == 12):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i+1] and (not Input[1][i+1]) and (not Input[0][i+2]) and Input[1][i+2]))
            except:
                pass
        pcNum = 3
        formulaFilename = "test0012"
    
    # 13.) (a0) U[2,3] (a1) *****
    elif(formNum == 13):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+2]) and Input[1][i+2] and (not Input[0][i+3]) and Input[1][i+3]) or (Input[0][i+2] and (not Input[1][i+2]) and (not Input[0][i+3]) and Input[1][i+3]))
            except:
                pass
        pcNum = 3
        formulaFilename = "test0013"
    
    # 14.) a0 & G[2] (a1)
    elif(formNum == 14):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[0][i] and (Input[1][i] and Input[1][i+1] and Input[1][i+2]))
            except:
                pass
        pcNum = 4
        formulaFilename = "test0014"
    
    # 15.) (!a1) & (a0)
    elif(formNum == 15):
        for i in range(0,len(Input[0])):
            Verdict.append((not Input[1][i]) and Input[0][i] )
        pcNum = 4
        formulaFilename = "test0015"
    
    # 16.) (a0 & a0) & (a1)
    elif(formNum == 16):
        for i in range(0,len(Input[0])):
            Verdict.append((Input[0][i] and Input[0][i]) and Input[1][i])
        pcNum = 4
        formulaFilename = "test0016"
    
    # 17.) (!(!a0)) & (a1)
    elif(formNum == 17):
        for i in range(0,len(Input[0])):
            Verdict.append((not (not (Input[0][i]))) and Input[1][i])
        pcNum = 5
        formulaFilename = "test0017"
    
    # 18.) !(a0 & a0)
    elif(formNum == 18):
        for i in range(0,len(Input[0])):
            Verdict.append(not(Input[0][i] and Input[0][i]))
        pcNum = 4
        formulaFilename = "test0018"
        
    # 19.) G[5] (a0 & a0)
    elif(formNum == 19):
        for i in range(0,len(Input[0])):
            try: 
                Verdict.append(Input[0][i] and Input[0][i+1] and Input[0][i+2] and Input[0][i+3] and Input[0][i+4] and Input[0][i+5])
            except:
                pass
        pcNum = 4
        formulaFilename = "test0019"
    
    # 20.) G[5] (!(!(a0 & a0))) = G[5] a0
    elif(formNum == 20):
        for i in range(0,len(Input[0])):
            try: 
                Verdict.append(Input[0][i] and Input[0][i+1] and Input[0][i+2] and Input[0][i+3] and Input[0][i+4] and Input[0][i+5])
            except:
                pass
        pcNum = 6
        formulaFilename = "test0020"
    
    # 21.) !(G[2] a0)
    elif(formNum == 21):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(not (Input[0][i] and Input[0][i+1] and Input[0][i+2]))
            except:
                pass
        pcNum = 3
        formulaFilename = "test0021"
    # 22.) (G[2] a0) & (G[2] a1)
    elif(formNum == 22):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and Input[0][i+1] and Input[0][i+2]) and (Input[1][i] and Input[1][i+1] and Input[1][i+2]))
            except:
                pass
        pcNum = 5
        formulaFilename = "test0022"
    
    # 23.) !(!a0) 
    elif(formNum == 23):
        for i in range(0,len(Input[0])):
            Verdict.append(not(not(Input[0][i])))
        pcNum = 3
        formulaFilename = "test0023"
    
    # 24.) G[5] a1
    elif(formNum == 24):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[1][i] and Input[1][i+1] and Input[1][i+2] and Input[1][i+3] and Input[1][i+4] and Input[1][i+5])
            except:
                pass
        pcNum = 2
        formulaFilename = "test0024"
    
    # 25.) !(G[2] (!a1) )
    elif(formNum == 25):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(not((not Input[1][i]) and (not Input[1][i+1]) and (not Input[1][i+2])))
            except:
                pass
        pcNum = 4
        formulaFilename = "test0025"
    
    # 26.) (G[2] a0) & (a1)
    elif(formNum == 26):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and Input[0][i+1] and Input[0][i+2]) and Input[1][i])
            except:
                pass
        pcNum = 4
        formulaFilename = "test0026"
    
    # 27.) !( (G[5,10] a0) & (G[2] a1) ))
    elif(formNum == 27):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i+5] and Input[0][i+6] and Input[0][i+7] and Input[0][i+8] and Input[0][i+9] and Input[0][i+10]) and (Input[1][i] and Input[1][i+1] and Input[1][i+1]))
            except:
                pass
        pcNum = 6
        formulaFilename = "test0027"
    
    # 28.) G[2](!(!a0)) & a1
    elif(formNum == 28):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and Input[0][i+1] and Input[0][i+2]) and Input[1][i])
            except:
                pass
        pcNum = 6
        formulaFilename = "test0028"
    
    # 29.) a1 & (G[0,8] a0)
    elif(formNum == 29):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[1][i] and (Input[0][i] and Input[0][i+1] and Input[0][i+2] and Input[0][i+3] and Input[0][i+4] and Input[0][i+5] and Input[0][i+6] and Input[0][i+7] and Input[0][i+8] ))
            except:
                pass
        pcNum = 4
        formulaFilename = "test0029"
    
    # 30.) (G[2] a1) & (G[5,10] a0)
    elif(formNum == 30):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[1][i] and Input[1][i+1] and Input[1][i+2]) and (Input[0][i+5] and Input[0][i+6] and Input[0][i+7] and Input[0][i+8] and Input[0][i+9] and Input[0][i+10]))
            except:
                pass
        pcNum = 5
        formulaFilename = "test0030"
    
    # 31.) G[2] a1
    elif(formNum == 31):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[1][i] and Input[1][i+1] and Input[1][i+2]))
            except:
                pass
        pcNum = 2
        formulaFilename = "test0031"
    
    # 32.) (a0 & a1) & (G[3,5] a0)
    elif(formNum == 32):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and Input[1][i]) and (Input[0][i+3] and Input[0][i+4] and Input[0][i+5]))
            except:
                pass
        pcNum = 2
        formulaFilename = "test0032"
    
    # 34.) a1 & F[5,10] a0
    elif(formNum == 34):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Inpit[1][i] and (Input[0][i+5] or Input[0][i+6]) or Input[0][i+7] or Input[0][i+8] or Input[0][i+9] or Input[0][i+10])
            except:
                pass
        pcNum = 4
        formulaFilename = "test0034"
    
    # 35.) G[2,4](G[2]a1)
    elif(formNum == 35):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(Input[1][i+2] and Input[1][i+3] and Input[1][i+4] and (Input[1][i] and Input[1][i+1] and Input[1][i+2]))
            except:
                pass
        pcNum = 4
        formulaFilename = "test0035"
    
    
    # Default
    else:
        return Input[0], -1, ""
    
    
    return Verdict, pcNum, formulaFilename
#------------------------------------------------------------------------------------#
# Method for saving oracle files
#------------------------------------------------------------------------------------#
def saveOracle(pcNum, Verdict, formulaFilename, numInput):       
    if(pcNum == -1):
        return -1
    
    # Format the filename of the input file name with the correct number of 0s
    if(numInput < 10):
        countInput = "0" + str(numInput)
    else:
        countInput = str(numInput)
    
    # Creat the oracle file
    filename = oracleDir + formulaFilename + "_" + inputFilename + countInput
    f = open(filename,'w+')
    
    f.write('**********RESULTS**********\n')
    
    for i in range(0,len(Verdict)):
        # If Verdict is 0 (False),
        if(Verdict[i]):
            Output = str(pcNum) + ':(' + str(i) + ',True)\n'
        # Else, Verdict is 1 (True),
        else:
            Output = str(pcNum) + ':(' + str(i) + ',False)\n'
        f.write(Output)

    # Close the file
    f.close()
 
#------------------------------------------------------------------------------------#
# Method for removing oracle files
#------------------------------------------------------------------------------------#
def removeOracle(numFormula, numInput):
    # Format the filename of the input file name with the correct number of 0s
    if(numFormula < 10):
        formulaFilename = "test000" + str(numFormula)
    else:
        formulaFilename = "test00" + str(numFormula)
    
    # Format the filename of the input file name with the correct number of 0s
    if(numInput < 10):
        countInput = "0" + str(numInput)
    else:
        countInput = str(numInput)
        
    filename = oracleDir + formulaFilename + "_" + inputFilename + countInput
    try:
        os.remove(filename)
    except:
        pass
#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# for removing the formula files
if(sys.argv[1] == '-r'):
    for i in range(0,NumFormulas):
        for j in range(0,NumInputs):
            removeOracle(i,j)
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    for i in range(0,NumFormulas):
        for j in range(0,NumInputs):
            AtomicInput = readInput(j)
            Verdict, pcNum, formulaFilename = getVerdict(i,AtomicInput)
            saveOracle(pcNum,Verdict,formulaFilename,j)
 
else:
    print("Invalid input arguement")
    print("-m to make the oracle files")
    print("-r to remove them")
