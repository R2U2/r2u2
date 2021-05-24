#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 17th, 2020
# File Name:   genOracle.py
# Description:
#------------------------------------------------------------------------------------#
import shutil
import sys
import os
from os import listdir
from os.path import isfile, join

# Paths to input and formula directories (from oracle directory)
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__OracleDir__    = __AbsolutePath__+'oracleFiles/'
__InputDir__     = __AbsolutePath__+'../Inputs/inputFiles/'
__TLDir__        = __AbsolutePath__+'../TL_formula/formulaFiles/'

#------------------------------------------------------------------------------------#
# Based on the input arguements, read in the input file and return the trace as a 2D
# array
#------------------------------------------------------------------------------------#
def readInput(_inputFile):

    # Open the input file and read the inputs
    f = open(__InputDir__ + _inputFile,'r').read()
    # Split the file object by rows
    lines = f.split('\n')

    # Create the Array list, which will store the inputs as a 2D list, where
    # the outer list corresponds to the atomics and the inner list corresponds to
    # each atomic's the time-steps
    Array = []

    # Determine the number of columns in the input file
    nCol = len(lines[0].split(','))
    for i in range(0,nCol):
        Array.append([])

    # Need a try statement or else there is an exception thrown when reading the
    # end-of-file charater
    try:
    # Read each row
        for line in lines:
            if line != "":
                # Split each row segment into columns
                part = line.split(',')
                # For all columns of that row,
                for j in range(0,len(part)):
                    # Append the number to the corresponding list
                    Array[j].append(int(part[j]))
    # If an exception is raised when parsing the input file, ignore it
    except EOFError:
        pass

    # Return the Array list
    return(Array)

#------------------------------------------------------------------------------------#
#
#------------------------------------------------------------------------------------#
def getVerdict(_formulaFile, Input):
    Verdict = []
    TimeStamp = []
    # 0.) !a0
    if(_formulaFile == "test0000"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not Input[0][i])
        pcNum = 2

    # 1.) (a0 & a1)
    elif(_formulaFile == "test0001"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(Input[0][i] and Input[1][i])
        pcNum = 3

    # 2.) G[0] (a0)
    elif(_formulaFile == "test0002"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(Input[0][i])
        pcNum = 2

    # 3.) G[5] (a0)
    elif(_formulaFile == "test0003"):
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

    # 4.) G[0,0] (a0)
    elif(_formulaFile == "test0004"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(Input[0][i])
        pcNum = 2

    # 5.) G[0,1] (a0)
    elif(_formulaFile == "test0005"):
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

    # 6.) G[5,10] (a0)
    elif(_formulaFile == "test0006"):
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

    # 7.) (a0) U[0,0] (a1) *****
    elif(_formulaFile == "test0007"):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((not Input[0][i]) and Input[1][i])
                TimeStamp.append(i)
            except IndexError:
                pass
        pcNum = 3

    # 8.) (a0) U[0,1] (a1) *****
    elif(_formulaFile == "test0008"):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append((Input[0][i] and (not Input[1][i]) and (not Input[0][i+1]) and Input[1][i+1]) or ((not Input[0][i]) and Input[1][i] and (not Input[0][i+1]) and Input[1][i+1]))
                TimeStamp.append(i)
            except IndexError:
                pass
        pcNum = 3

    # 9.) (a0) U[5,10] (a1) *****
    elif(_formulaFile == "test0009"):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+5]) and Input[1][i+5] and (not Input[0][i+6]) and Input[1][i+6] and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10])or (Input[0][i+5] and (not Input[1][i+5]) and (not Input[0][i+6]) and Input[1][i+6] and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and (not Input[0][i+7]) and Input[1][i+7] and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and (not Input[0][i+8]) and Input[1][i+8] and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and Input[0][i+8] and (not Input[1][i+8]) and (not Input[0][i+9]) and Input[1][i+9] and (not Input[0][i+10]) and Input[1][i+10]) or (Input[0][i+5] and (not Input[1][i+5]) and Input[0][i+6] and (not Input[1][i+6]) and Input[0][i+7] and (not Input[1][i+7]) and Input[0][i+8] and (not Input[1][i+8]) and Input[0][i+9] and (not Input[1][i+9]) and (not Input[0][i+10]) and Input[1][i+10]))
                TimeStamp.append(i)
            except IndexError:
                pass
        pcNum = 3

    # 10.) (a0) U[0,2] (a1) *****
    elif(_formulaFile == "test0010"):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i]) and Input[1][i] and (not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i] and (not Input[1][i]) and (not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i] and (not Input[1][i]) and Input[0][i+1] and (not Input[1][i+1]) and (not Input[0][i+2]) and Input[1][i+2]))
                TimeStamp.append(i)
            except IndexError:
                pass
        pcNum = 3

    # 12.) (a0) U[1,2] (a1) *****
    elif(_formulaFile == "test0012"):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+1]) and Input[1][i+1] and (not Input[0][i+2]) and Input[1][i+2]) or (Input[0][i+1] and (not Input[1][i+1]) and (not Input[0][i+2]) and Input[1][i+2]))
                TimeStamp.append(i)
            except IndexError:
                pass
        pcNum = 3

    # 13.) (a0) U[2,3] (a1) *****
    elif(_formulaFile == "test0013"):
        for i in range(0,len(Input[0])):
            try:
                Verdict.append(((not Input[0][i+2]) and Input[1][i+2] and (not Input[0][i+3]) and Input[1][i+3]) or (Input[0][i+2] and (not Input[1][i+2]) and (not Input[0][i+3]) and Input[1][i+3]))
                TimeStamp.append(i)
            except IndexError:
                pass
        pcNum = 3

    # 14.) a0 & G[2] (a1)
    elif(_formulaFile == "test0014"):
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

    # 15.) (!a1) & (a0)
    elif(_formulaFile == "test0015"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((not Input[1][i]) and Input[0][i])
        pcNum = 4

    # 16.) (a0 & a0) & (a1)
    elif(_formulaFile == "test0016"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((Input[0][i] and Input[0][i]) and Input[1][i])
        pcNum = 4

    # 17.) (!(!a0)) & (a1)
    elif(_formulaFile == "test0017"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((not (not (Input[0][i]))) and Input[1][i])
        pcNum = 5

    # 18.) !(a0 & a0)
    elif(_formulaFile == "test0018"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not(Input[0][i] and Input[0][i]))
        pcNum = 4

    # 19.) G[5] (a0 & a0)
    elif(_formulaFile == "test0019"):
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

    # 20.) G[5] (!(!(a0 & a0))) = G[5] a0
    elif(_formulaFile == "test0020"):
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

    # 21.) !(G[2] a0)
    elif(_formulaFile == "test0021"):
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

    # 22.) (G[2] a0) & (G[2] a1)
    elif(_formulaFile == "test0022"):
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

    # 23.) !(!a0)
    elif(_formulaFile == "test0023"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not(not(Input[0][i])))
        pcNum = 3

    # 24.) G[5] a1
    elif(_formulaFile == "test0024"):
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

    # 25.) !(G[2] (!a1) )*****
    elif(_formulaFile == "test0025"):
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

    # 26.) (G[2] a0) & (a1)
    elif(_formulaFile == "test0026"):
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

    # 27.) !( (G[5,10] a0) & (G[2] a1) ))
    elif(_formulaFile == "test0027"):
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

    # 28.) G[2](!(!a0)) & a1
    elif(_formulaFile == "test0028"):
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

    # 29.) a1 & (G[0,8] a0)
    elif(_formulaFile == "test0029"):
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

    # 30.) (G[2] a1) & (G[5,10] a0)
    elif(_formulaFile == "test0030"):
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

    # 31.) G[2] a1
    elif(_formulaFile == "test0031"):
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

    # 32.) (a0 & a1) & (G[3,5] a0)
    elif(_formulaFile == "test0032"):
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

    # 33.) a1 & (G[8] a0)
    elif(_formulaFile == "test0033"):
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
            # and a1 is true at this time stamp, G[8] a0 is true 
            # at the current time stamp. 
            if((Counter <= LB) and (int(Input[1][i]) == 1)): 
                TimeStamp.append(i-UB+LB+1)
                Verdict.append(False)
            # Or if the counter equals the upper bound, then the 
            # G[8] a0 is false at the current time stamp. 
            elif(Counter == UB):
                TimeStamp.append(i)
                Verdict.append(True)
        pcNum = 4

    # 34.) a1 & F[5,10] a0
    elif(_formulaFile == "test0034"):
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

    # 35.) G[2,4](G[2]a1)
    elif(_formulaFile == "test0035"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4

    # 36.) All formulas
    elif(_formulaFile == "test0036"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4


    # 37.) H[5,10] a0
    elif(_formulaFile == "test0037"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 2

    # 38.) (a0) S[0,2] (a1)
    elif(_formulaFile == "test0038"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 3

    # 39.) H[2] a1
    elif(_formulaFile == "test0039"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 2

    # 40.) a1 & O[5,10] a0
    elif(_formulaFile == "test0040"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4

    # 41.) a1 -> a0 = (!a1 | a0
    elif(_formulaFile == "test0041"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((not Input[1][i]) or Input[0][i])
        pcNum = 4

    # 42.) a1 <-> a0 = (a1 -> a0) & (a0 -> a1) = (!a1 | a0) & (!a0 | a1)
    elif(_formulaFile == "test0042"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append((Input[1][i] or (not Input[0][i])) and ((not Input[1][i]) or Input[0][i]))
        pcNum = 4

    # 43.) !(a1 | a0)
    elif(_formulaFile == "test0043"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(not (Input[1][i] or Input[0][i]))
        pcNum = 4

    # 44.) tests 6, 10, 15, 31, 34, 37-43
    elif(_formulaFile == "test0044"):
        for i in range(0,len(Input[0])):
            TimeStamp.append(i)
            Verdict.append(False)
        pcNum = 4

    else:
        print('Unknown formula file:' + _formulaFile)
        return -1,False, -1


    return TimeStamp, Verdict, pcNum

#------------------------------------------------------------------------------------#
# Method for Global Operator
#------------------------------------------------------------------------------------#

#------------------------------------------------------------------------------------#
# Method for saving oracle files
#------------------------------------------------------------------------------------#
def saveOracle(pcNum, TimeStamp, Verdict, filename):
    # If there is no known formula
    if(pcNum == -1):
        return -1

    # Creat the oracle file
    f = open(filename,'w+')

    # Print the header
    f.write('**********RESULTS**********\n')

    # If there is a mismatch in the TimeStamp and Verdict,
    if(len(TimeStamp) != len(Verdict)):
        # Print the filename
        print(filename)

    for i in range(0,len(Verdict)):
        # If Verdict is 0 (False),
        if(Verdict[i]):
            Output = str(pcNum) + ':' + str(TimeStamp[i]) + ',T\n'
        # Else, Verdict is 1 (True),
        else:
            Output = str(pcNum) + ':' + str(TimeStamp[i]) + ',F\n'
        f.write(Output)

    # Close the file
    f.close()

#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# If there are no arguements
if len(sys.argv) == 1:
    print("ERROR: Missing input arguement")
    print("Use '-h' flag for more information")
    exit()

# See if oracleFiles directory exists; if not make, items
if(not os.path.isdir(__OracleDir__)):
    os.mkdir(__OracleDir__)

# for removing the formula files
if(sys.argv[1] == '-r'):
    shutil.rmtree(__OracleDir__)

# for generating the formula files
elif(sys.argv[1] == '-m'):
    # Grab all the formulas in the TL_formula/formulaFiles/ directory and
    # grab all the inputs in the Inputs/inputFiles/ directory
    formulaFiles,inputFiles = [[f for f in listdir(i) if isfile(join(i, f))] for i in (__TLDir__,__InputDir__)]
    # For each formula file,
    for _formulaFile in formulaFiles:
        # Pull off the '.mltl' of the fromula filename
        formula = _formulaFile.replace('.mltl','')
        # For each input file,
        for _inputFile in inputFiles:
            # Parse the input file into a list
            AtomicInput = readInput(_inputFile)
            # Pull off the '.csv' of the input filename
            input = _inputFile.replace('.csv','')
            # Generate the oracles output file name
            filename = __OracleDir__ + formula + '_' + input + '.txt'
            # Determine the verdict for the given formula and input
            TimeStamp, Verdict, pcNum = getVerdict(formula,AtomicInput)
            # Save the Oracle output, if it is valid
            saveOracle(pcNum, TimeStamp, Verdict, filename)
    print('Oracle files are located in the '+__OracleDir__+' directory')

else:
    print("Invalid input arguement")
    print("-m to make the oracle files")
    print("-r to remove them")
