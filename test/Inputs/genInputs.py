#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 7th, 2020
# File Name:   genInputs.py
# Description: A Python 3 script used to generate inputs for various test cases used
#              for R2U2 regression testing. Note that this script is built using the 
#              old Matlab script, "genInputs.m", as a template.
#------------------------------------------------------------------------------------#
import numpy as np
import csv
import sys
import os

nRow = 31
nCol = 2

numInputs = 53

def makeInputs():
    global nRow, nCol
    #------------------------------------------------------------------------------------#
    # 0.) Both all zeros test cases
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0000'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            Array[i].append(0.0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")


    #------------------------------------------------------------------------------------#
    # 1.) Both all ones test cases
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0001'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 2.) First Input All True, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0002'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 3.) First Input All False, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0003'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 4.) First Input All True, Second Input Oscillating between false and true
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0004'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            elif(j == 1):
                if(np.mod(i,2) == 0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 5.) First Input All True, Second Input Oscillating between true and false
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0005'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            elif(j == 1):
                if(np.mod(i,2) == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 6.) First Input All False, Second Input Oscillating between false and true
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0006'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(0)
            elif(j == 1):
                if(np.mod(i,2) == 0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 7.) First Input All False, Second Input Oscillating between true and false
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0007'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            elif(j == 1):
                if(np.mod(i,2) == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 8.) First Input Oscillating between false and true, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0008'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                if(np.mod(i,2) == 0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 9.) First Input Oscillating between true and false, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0009'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                if(np.mod(i,2) == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 10.) First Input Oscillating between false and true, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0010'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                if(np.mod(i,2) == 0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 11.) First Input Oscillating between true and false, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0011'

    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                if(np.mod(i,2) == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 12.) First Input Five Time Step Pulse Wave, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0012'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 13.) First Input Five Time Step Pulse Wave, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0013'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 14.) First Input Five Time Step Pulse Wave, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0014'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 15.) First Input Five Time Step Pulse Wave, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0015'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 16.) First Input All True, Second Input Five Time Step Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0016'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            elif(j == 1):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 17.) First Input All False, Second Input Five Time Step Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0017'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(0)
            elif(j == 1):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 18.) First Input All True, Second Input Five Time Step Inverse Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0018'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            elif(j == 1):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 19.) First Input All False, Second Input Five Time Step Inverse Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0019'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
            
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(0)
            elif(j == 1):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 20.) Both Inputs are 5 time step pulse waves
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0020'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
        
        for j in range(0,nCol):
            if(flip):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 21.) First Input 5 time step Inverse Pulse Wave. Second Input 5 time step pulse wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0021'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
        
        for j in range(0,nCol):
            if(flip):
                if(j == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                if(j == 0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 22.) First Input 5 time step Inverse Pulse Wave. Second Input 5 time step pulse wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0022'

    Array = []
    flip = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
        
        for j in range(0,nCol):
            if(flip):
                if(j == 0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                if(j == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 23.) Both Inputs are 5 time step pulse waves
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0023'

    Array = []
    flip = False
    for i in range(0,nRow):
        Array.append([])
        # Toggle 'flip' every 5 rows
        if(np.mod(i,5) == 0):
            flip = not(flip)
        
        for j in range(0,nCol):
            if(flip):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 24.) Both Inputs are five time step pulses, with the second input shifted right by 3
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0024'

    Array = []
    flip1 = True
    flip2 = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input
        if(np.mod(i,5) == 0):
            flip1 = not flip1
        # Toggle flag for the second input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip2 = not flip2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 25.)  Both Inputs are five time step pulses, with the second input shifted right by 3
    #       First Input Wave is inverse wave.
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0025'

    Array = []
    flip1 = True
    flip2 = False
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input
        if(np.mod(i,5) == 0):
            flip1 = not flip1
        # Toggle flag for the second input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip2 = not flip2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 26.)  Both Inputs are five time step pulses, with the second input shifted right by 3
    #       Second Wave is Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0026'

    Array = []
    flip1 = True
    flip2 = False
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input
        if(np.mod(i,5) == 0):
            flip1 = not flip1
        # Toggle flag for the second input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip2 = not flip2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")


    #------------------------------------------------------------------------------------#
    # 27.) Both Inputs are five time step pulses, with the second input shifted right by 3
    #      First and second waves are Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0027'

    Array = []
    flip1 = True
    flip2 = False
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input
        if(np.mod(i,5) == 0):
            flip1 = not flip1
        # Toggle flag for the second input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip2 = not flip2
            
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 28.) Both Inputs are five time step pulses, with the first input shifted right by 3
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0028'

    Array = []
    flip1 = False
    flip2 = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip1 = not flip1
        # Toggle flag for the second input
        if(np.mod(i,5) == 0):
            flip2 = not flip2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 29.)  Both Inputs are five time step pulses, with the first input shifted right by 3
    #       Scond Input Wave is inverse wave.
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0029'

    Array = []
    flip1 = False
    flip2 = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip1 = not flip1
        # Toggle flag for the second input
        if(np.mod(i,5) == 0):
            flip2 = not flip2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 30.)  Both Inputs are five time step pulses, with the first input shifted right by 3
    #       First Wave is Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0030'

    Array = []
    flip1 = False
    flip2 = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip1 = not flip1
        # Toggle flag for the second input
        if(np.mod(i,5) == 0):
            flip2 = not flip2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")


    #------------------------------------------------------------------------------------#
    # 31.) Both Inputs are five time step pulses, with the second input shifted right by 3
    #      First and second waves are Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0031'

    Array = []
    flip1 = False
    flip2 = True
    for i in range(0,nRow):
        Array.append([])
        # Toggle flag for the first input, offset by 3 time stamps
        if(np.mod(i-3,5) == 0 and i > 3):
            flip1 = not flip1
        # Toggle flag for the second input
        if(np.mod(i,5) == 0):
            flip2 = not flip2
            
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip1):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip2):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 32.) Figure 4.39
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0032'

    Array = []
    for i in range(0,nRow):
        Array.append([])
            
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if((i >= 1) and (i <= 5)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if((i >= 4) and (i <= 8)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 33.) Example for TACAS14 Paper
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0033'

    Array = []
    for i in range(0,nRow):
        Array.append([])
            
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if((i >= 11) and (i <= 25)) :
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(((i >= 3) and (i <= 10)) or (i == 13) or ((i >= 15) and (i <= 18)) or ((i >= 21) and (i <= 24)) or ((i >= 26) and (i <= 28))):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 34.) test AND operation
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0034'

    Array = []
    for i in range(0,nRow):
        Array.append([])
            
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if((i >= 5) and (i <= 30)) :
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if((i >= 2) and (i <= 30)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 35.) First Input all True; Second Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0035'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 36.) First Input all True; Second Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0036'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 37.) First Input all True; Second Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0037'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 38.) First Input all True; Second Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0038'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 39.) Second Input all True; First Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0039'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 40.) Second Input all True; First Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0040'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 41.) Second Input all True; First Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0041'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 42.) Second Input all True; First Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0042'

    Array = []
    flip = True
    counter = 1
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter * 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 43.) First Input all True; Second Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0043'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 44.) First Input all True; Second Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0044'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(1)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 45.) First Input all True; Second Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0045'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 46.) First Input all True; Second Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0046'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                Array[i].append(0)
            # The second input
            elif(j == 1):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 47.) Second Input all True; First Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0047'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 48.) Second Input all True; First Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0048'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 49.) Second Input all True; First Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0049'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 50.) Second Input all True; First Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0050'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 16) or (i == 24)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")

    #------------------------------------------------------------------------------------#
    # 51.) 
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0051'

    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input
        if(np.mod(i,counter) == 0):
            flip = not flip
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter = counter / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(i == 0):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                Array[i].append(1)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")


    #------------------------------------------------------------------------------------#
    # 52.) Pei Test Input
    #------------------------------------------------------------------------------------#
    # Create the file
    #filename = 'tacas'
    filename = 'input0052'
    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
       
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if((i >= 11) and (i <= 25)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(((i >= 4) and (i <= 11)) or (i == 14) or ((i >= 16) and (i <= 19)) or ((i >= 22) and (i <= 25)) or ((i >= 27) and (i <= 29)) or (i >= 32)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt('inputFiles/' + filename,Array,fmt="%1.6f",delimiter=",")



#------------------------------------------------------------------------------------#
# Method for removing formula files
#------------------------------------------------------------------------------------#
def removeInputs():
    global numInputs
    for i in range(0,numInputs):
        # Format the filename of the input file name with the correct number of 0s
        if(i < 10):
            inputFilename = "input000" + str(i)
        else:
            inputFilename = "input00" + str(i)
            
        filename = "inputFiles/" + inputFilename
        try:
            os.remove(filename)
        except:
            pass

#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# for removing the formula files
if(sys.argv[1] == '-r'):
    removeInputs()
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    makeInputs()
 
else:
    print("Invalid input arguement")
    print("-m to make the formula files")
    print("-r to remove them")  