#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 17th, 2020
# File Name:   genOracle.py
# Description: 
#------------------------------------------------------------------------------------#
import shutil
import sys
import os

# Paths to input and formula directories (from oracle directory)
inputDir     = '../Inputs/inputFiles/'
oracleDir  = 'oracleFiles/'

# Filenames for each file type
inputFilename   = "input00"

# Number of input files
NumInputs = 54
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
    f = open(inputDir+inputFilename+Count+'.csv','r').read()
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
            for j in range(0,len(part)):
                # Append the number to the corresponding list
                Array[j].append(int(part[j]))        
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
    TimeStamp = []
    # 0.) !a0
    if(formNum == 0):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not Input[0][i])
        pcNum = 2
        formulaFilename = "test0000"
        
    # 1.) (a0 & a1)
    elif(formNum == 1):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(Input[0][i] and Input[1][i])
        pcNum = 3
        formulaFilename = "test0001"
        
    # 2.) G[0] (a0)
    elif(formNum == 2):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(Input[0][i])
        pcNum = 2
        formulaFilename = "test0002"
        
    # 3.) G[5] (a0)
    elif(formNum == 3):
        LB = 0
        UB = 5
        Counter = UB
        for i in range(0,len(Input[0])):
            # If we are True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # If we are False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # G[5] a0 is true at the earliest time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[5] a0 is false at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0003"
        
    # 4.) G[0,0] (a0)
    elif(formNum == 4):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(Input[0][i])
        pcNum = 2
        formulaFilename = "test0004"
        
    # 5.) G[0,1] (a0)
    elif(formNum == 5):
        LB = 0
        UB = 1
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # If a0 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # G[0,1] (a0) is true at the earliest time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[0,1] (a0) is false at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0005"
        
    # 6.) G[5,10] (a0)
    elif(formNum == 6):
        LB = 5
        UB = 10
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # If a0 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # G[5,10] (a0) is true at earliest time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[5,10] (a0) is false at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0006"
        
    # 7.) (a0) U[0,0] (a1) *****
    elif(formNum == 7):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((not Input[0][i]) and Input[1][i])
                TimeStamp.append(i)
            except:
                pass
        pcNum = 3
        formulaFilename = "test0007"
    
    # 8.) (a0) U[0,1] (a1) *****
    elif(formNum == 8):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and (not Input[1][i]) and (not Input[0][i+1]) and Input[1][i+1]) or ((not Input[0][i]) and Input[1][i] and (not Input[0][i+1]) and Input[1][i+1]))
                TimeStamp.append(i)
            except:
                pass
        pcNum = 3
        formulaFilename = "test0008"
    
    # 9.) (a0) U[5,10] (a1) *****
    elif(formNum == 9):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+5]) and Input[1][i+5] and (not Input[0][i+6]) and Input[1][i+6] and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10])or (Input[0][i+5] and (not Input[1][i+5]) and (not Input[0][i+6]) and Input[1][i+6] and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and Input[0][i+8] and (not Input[1][i+8]) and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and Input[0][i+8] and (not Input[1][i+8]) and Input[0][i+9] and (not Input[1][i+9]) and (not Input[0][i+10]) and Input[1][i+10]))
                TimeStamp.append(i)
            except:
                pass
        pcNum = 3
        formulaFilename = "test0009"
    
    # 10.) (a0) U[0,2] (a1) *****
    elif(formNum == 10):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i]) and Input[1][i] and (not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i] and (not Input[1][i]) and (not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i] and (not Input[1][i]) and Input[0][i+1] and (not Input[1][i+1]) and (not Input[0][i+2]) and Input[1][i+2]))
                TimeStamp.append(i)
            except:
                pass
        pcNum = 3
        formulaFilename = "test0010"
    
    # 12.) (a0) U[1,2] (a1) *****
    elif(formNum == 12):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i+1] and (not Input[1][i+1]) and (not Input[0][i+2]) and Input[1][i+2]))
                TimeStamp.append(i)
            except:
                pass
        pcNum = 3
        formulaFilename = "test0012"
    
    # 13.) (a0) U[2,3] (a1) *****
    elif(formNum == 13):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+2]) and Input[1][i+2] and (not Input[0][i+3]) and Input[1][i+3]) or (Input[0][i+2] and (not Input[1][i+2]) and (not Input[0][i+3]) and Input[1][i+3]))
                TimeStamp.append(i)
            except:
                pass
        pcNum = 3
        formulaFilename = "test0013"
    
    # 14.) a0 & G[2] (a1)
    elif(formNum == 14):
        LB = 0
        UB = 2
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a1 are True at t = 0
            if(int(Input[1][i]) == 1):
                Counter = Counter - 1
            # Else a1 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # the G[2] a1 is true, at the earliest time stamp. 
            if(Counter <= LB) and (int(Input[0][i]) == 1):
                TimeStamp.append(i-UB+LB+1) 
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[2] a0 is false at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0014"
    
    # 15.) (!a1) & (a0)
    elif(formNum == 15):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((not Input[1][i]) and Input[0][i])
        pcNum = 4
        formulaFilename = "test0015"
    
    # 16.) (a0 & a0) & (a1)
    elif(formNum == 16):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((Input[0][i] and Input[0][i]) and Input[1][i])
        pcNum = 4
        formulaFilename = "test0016"
    
    # 17.) (!(!a0)) & (a1)
    elif(formNum == 17):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((not (not (Input[0][i]))) and Input[1][i])
        pcNum = 5
        formulaFilename = "test0017"
    
    # 18.) !(a0 & a0)
    elif(formNum == 18):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not(Input[0][i] and Input[0][i]))
        pcNum = 4
        formulaFilename = "test0018"
        
    # 19.) G[5] (a0 & a0)
    elif(formNum == 19):
        LB = 0
        UB = 5
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # If a0 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # the G[5] a0 is true at the current time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[5] a0 is false at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0019"
    
    # 20.) G[5] (!(!(a0 & a0))) = G[5] a0
    elif(formNum == 20):
        LB = 0
        UB = 5
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter = Counter - 1
            # If a0 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # the G[5] a0 is true, at the current time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # G[2] a0 is false at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 6
        formulaFilename = "test0020"
    
    # 21.) !(G[2] a0)
    elif(formNum == 21):
        LB = 0
        UB = 2
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                # Decrement the counter
                Counter = Counter - 1
            # If a0 is False at t = 0
            else:
                # Reset the counter
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # the G[2] a0 is true, so !(G[2] a0) is false at the 
            # current time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # G[2] a0 is false, so !(G[2] a0) is true at the 
            # current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 3
        formulaFilename = "test0021"
        
    # 22.) (G[2] a0) & (G[2] a1)
    elif(formNum == 22):
        LB = 0
        UB = 2
        Counter0 = UB
        Counter1 = UB
        for i in range(0,len(Input[0])):
            #----- Global for a0 -----#
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                # Decrement counter0
                Counter0 = Counter0 - 1
            # If a0 is False at t = 0
            else:
                # Reset counter0
                Counter0 = UB
            
            #----- Global for a1 -----#
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                # Decrement counter1
                Counter1 = Counter1 - 1
            # If a1 is False at t = 0
            else:
                # Reset counter1
                Counter1 = UB
            
            #----- And both Globals -----#
            # If both counters are equal to or below the lower bound,
            # then the verdict is True at the current time stamp. 
            if((Counter0 <= LB) and (Counter1 <= LB)):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if either counter equals the upper bound, then the 
            # verdict is False at the current time stamp.    
            elif((Counter0 == UB) or (Counter1 == UB)):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 5
        formulaFilename = "test0022"
    
    # 23.) !(!a0) 
    elif(formNum == 23):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not(not(Input[0][i])))
        pcNum = 3
        formulaFilename = "test0023"
    
    # 24.) G[5] a1
    elif(formNum == 24):
        LB = 0
        UB = 5
        Counter = UB
        for i in range(0,len(Input[1])):
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter = Counter - 1
            # If a1 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # we are True at the current time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # we are False at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0024"
    
    # 25.) !(G[2] (!a1) )*****
    elif(formNum == 25):
        LB = 0
        UB = 2
        Counter = UB
        for i in range(0,len(Input[1])):
            # If !a1 is True at t = 0
            if(int(Input[1][i]) == 0):
                Counter = Counter - 1
            # If !a1 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # we are False at the current time stamp. 
            if(Counter <= LB):
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # we are True at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 4
        formulaFilename = "test0025"
    
    # 26.) (G[2] a0) & (a1)
    elif(formNum == 26):
        LB = 0
        UB = 2
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # Else, a0 is False at t = 0
            else:
                Counter = UB
            
            # If the counter is equal to or below our lower bound,
            # we are True at the current time stamp. 
            if(Counter <= LB and Input[1][i]): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # we are False at the current time stamp.
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False) 
        pcNum = 4
        formulaFilename = "test0026"
    
    # 27.) !( (G[5,10] a0) & (G[2] a1) ))
    elif(formNum == 27):
        LB0 = 5
        UB0 = 10
        LB1 = 0
        UB1 = 2
        Counter0 = UB0
        Counter1 = UB1
        for i in range(0,len(Input[0])):
            #----- G[5,10] a0 -----#
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter0 = Counter0 - 1
            # Else, a0 is False at t = 0
            else:
                Counter0 = UB0
            
            #----- G[2] a1 -----#
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter1 = Counter1 - 1
            # Else, a1 is False at t = 0
            else:
                Counter1 = UB0
                
            #----- And & negation of both globals -----#
            # If both counters are equal to or below their lower bound,
            # ((G[5,10] a0) & (G[2] a1)) is true, so its negation is
            # false at the current time stamp. 
            if((Counter0 <= LB0) and (Counter1 <= LB1)): 
                TimeStamp.append(i)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # ((G[5,10] a0) & (G[2] a1)) is false, so its negation is
            # true at the current time stamp. 
            elif((Counter0 == UB0) or (Counter1 == UB1)):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 6
        formulaFilename = "test0027"
    
    # 28.) G[2](!(!a0)) & a1
    elif(formNum == 28):
        LB = 0
        UB = 2
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # Else, a0 is False at t = 0
            else:
                Counter = UB

            # If the counter is equal to or below their lower bound,
            # and a1 is true at this time stamp, G[2] a0 is true at 
            # the current time stamp. 
            if((Counter <= LB) and (int(Input[1][i]) == 1)): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # G[2] a0 is false at the current time stamp. 
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 6
        formulaFilename = "test0028"
    
    # 29.) a1 & (G[0,8] a0)
    elif(formNum == 29):
        LB = 0
        UB = 8
        Counter = UB
        for i in range(0,len(Input[0])):
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter = Counter - 1
            # Else, a0 is False at t = 0
            else:
                Counter = UB

            # If the counter is equal to or below their lower bound,
            # and a1 is true at this time stamp, G[0,8] a0 is true 
            # at the current time stamp. 
            if((Counter <= LB) and (int(Input[1][i]) == 1)): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # G[0,8] a0 is false at the current time stamp. 
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 4
        formulaFilename = "test0029"
    
    # 30.) (G[2] a1) & (G[5,10] a0)
    elif(formNum == 30):
        LB0 = 5
        UB0 = 10
        LB1 = 0
        UB1 = 2
        Counter0 = UB0
        Counter1 = UB1
        for i in range(0,len(Input[0])):
            #----- G[5,10] a0 -----#
            # If a0 is True at t = 0
            if(int(Input[0][i]) == 1):
                Counter0 = Counter0 - 1
            # Else, a0 is False at t = 0
            else:
                Counter0 = UB0
            
            #----- G[2] a1 -----#
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter1 = Counter1 - 1
            # Else, a1 is False at t = 0
            else:
                Counter1 = UB0
                
            #----- And & negation of both globals -----#
            # If both counters are equal to or below their lower bound,
            # ((G[5,10] a0) & (G[2] a1)) is true, so its negation is
            # false at the current time stamp. 
            if((Counter0 <= LB0) and (Counter1 <= LB1)): 
                TimeStamp.append(i)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # ((G[5,10] a0) & (G[2] a1)) is false, so its negation is
            # true at the current time stamp. 
            elif((Counter0 == UB0) or (Counter1 == UB1)):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 5
        formulaFilename = "test0030"
    
    # 31.) G[2] a1
    elif(formNum == 31):
        LB = 0
        UB = 2
        Counter = UB
        for i in range(0,len(Input[1])):
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter = Counter - 1
            # Else, a1 is False at t = 0
            else:
                Counter = UB

            # If the counter is equal to or below their lower bound,
            # G[2] a1 is true at the current time stamp. 
            if(Counter <= LB): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[2] a1 is false at the current time stamp. 
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0031"
    
    # 32.) (a0 & a1) & (G[3,5] a0)
    elif(formNum == 32):
        LB = 3
        UB = 5
        Counter = UB
        for i in range(0,len(Input[1])):
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter = Counter - 1
            # Else, a1 is False at t = 0
            else:
                Counter = UB

            # If the counter is equal to or below their lower bound,
            # G[3,5] a0 is true and a0 = a1 = True at the current time stamp. 
            if((Counter <= LB) and Input[0][i] and Input[1][i]): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[3,5] a0 is false at the current time stamp. 
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0032"
    
    # 34.) a1 & F[5,10] a0
    elif(formNum == 34):
        LB = 5
        UB = 10
        Counter = LB
        for i in range(0,len(Input[1])):
            # If a1 is True at t = 0
            if(int(Input[1][i]) == 1):
                Counter = Counter + 1
            # Else, a1 is False at t = 0
            else:
                Counter = LB

            # If the counter is greater than its lower bound,
            # F[5,10] a0 is true and a1 is True at the
            # current time stamp. 
            if((Counter > LB) and Input[0][i] and Input[1][i]): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(True)
            # Or if the counter equals the upper bound, then the 
            # G[3,5] a0 is false at the current time stamp. 
            elif(Counter == LB):
                TimeStamp.append(i)
                Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0034"
    
    # 35.) G[2,4](G[2]a1)
    elif(formNum == 35):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0035"
    
    # 36.) All formulas
    elif(formNum == 36):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0036"
        
    
    # 37.) H[5,10] a0
    elif(formNum == 37):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0037"
    
    # 38.) (a0) S[0,2] (a1)
    elif(formNum == 38):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 3
        formulaFilename = "test0038"
        
    # 39.) H[2] a1
    elif(formNum == 39):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 2
        formulaFilename = "test0039"
        
    # 40.) a1 & O[5,10] a0
    elif(formNum == 40):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0040"
        
    # 41.) a1 -> a0 = (!a1 | a0
    elif(formNum == 41):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((not Input[1][i]) or Input[0][i])
        pcNum = 4
        formulaFilename = "test0041"
        
    # 42.) a1 <-> a0 = (a1 -> a0) & (a0 -> a1) = (!a1 | a0) & (!a0 | a1)
    elif(formNum == 42):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((Input[1][i] or (not Input[0][i])) and ((not Input[1][i]) or Input[0][i]))
        pcNum = 4
        formulaFilename = "test0042"
        
    # 43.) !(a1 | a0)
    elif(formNum == 43):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not (Input[1][i] or Input[0][i]))
        pcNum = 4
        formulaFilename = "test0043"    
    
    # 44.) tests 6, 10, 15, 31, 34, 37-43
    elif(formNum == 44):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4
        formulaFilename = "test0044"  
    
    
    
    # Default
    else:
        return -1,False, -1, ""
    
    
    return TimeStamp, Verdict, pcNum, formulaFilename
#------------------------------------------------------------------------------------#
# Method for saving oracle files
#------------------------------------------------------------------------------------#
def saveOracle(pcNum, TimeStamp, Verdict, formulaFilename, numInput):       
    if(pcNum == -1):
        return -1
    
    # Format the filename of the input file name with the correct number of 0s
    if(numInput < 10):
        countInput = "0" + str(numInput)
    else:
        countInput = str(numInput)
    
    # Creat the oracle file
    filename = oracleDir+formulaFilename+"_"+inputFilename+countInput+'.txt'
    f = open(filename,'w+')
    
    f.write('**********RESULTS**********\n')
    
    if(len(TimeStamp) != len(Verdict)):
        print(filename)
        
    for i in range(0,len(Verdict)):
        # If Verdict is 0 (False),
        if(Verdict[i]):
            Output = str(pcNum) + ':(' + str(TimeStamp[i]) + ',T)\n'
        # Else, Verdict is 1 (True),
        else:
            Output = str(pcNum) + ':(' + str(TimeStamp[i]) + ',F)\n'
        f.write(Output)

    # Close the file
    f.close()
 
#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# If there are no arguements
try:
    sys.argv[1]
except:
    print("ERROR: Missing input arguement")
    print("Use '-h' flag for more information")
    exit()

# See if oracleFiles directory exists; if not make, items
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
if(not os.path.isdir(__AbsolutePath__+'oracleFiles')):
    os.mkdir(__AbsolutePath__+'oracleFiles')

# for removing the formula files
if(sys.argv[1] == '-r'):
    shutil.rmtree(__AbsolutePath__+'oracleFiles')
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    for i in range(0,NumFormulas):
        for j in range(0,NumInputs):
            AtomicInput = readInput(j)
            TimeStamp, Verdict, pcNum, formulaFilename = getVerdict(i,AtomicInput)
            saveOracle(pcNum,TimeStamp, Verdict,formulaFilename,j)
 
else:
    print("Invalid input arguement")
    print("-m to make the oracle files")
    print("-r to remove them")
