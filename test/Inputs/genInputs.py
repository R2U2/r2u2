#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 16th, 2020
# File Name:   genInputs.py
# Description: A Python 3 script used to generate inputs for various test cases used
#              for R2U2 regression testing. Note that this script is built using the 
#              old Matlab script, "genInputs.m", as a template.
#------------------------------------------------------------------------------------#
import shutil
import numpy as np
import csv
import sys
import os

nRow = 31
nCol = 2

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__InputDir__     = __AbsolutePath__+'inputFiles/'

HEADER = 'a0,a1'

def makeInputs():
    global nRow, nCol
    #------------------------------------------------------------------------------------#
    # 0.) Both all zeros test cases
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0000'
    f = open(__InputDir__ + filename + '.csv','wb')
    
    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            Array[i].append(0.0)

    # Save the array to a .csv file
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 1.) Both all ones test cases
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0001'
    f = open(__InputDir__ + filename + '.csv','wb')
    
    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 2.) First Input All True, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0002'
    f = open(__InputDir__ + filename + '.csv','wb')
    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(1)
            else:
                Array[i].append(0)

    # Save the array to a .csv file
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 3.) First Input All False, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0003'
    f = open(__InputDir__ + filename + '.csv','wb')
    Array = []
    for i in range(0,nRow):
        Array.append([])
        for j in range(0,nCol):
            if(j == 0):
                Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 4.) First Input All True, Second Input Oscillating between false and true
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0004'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 5.) First Input All True, Second Input Oscillating between true and false
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0005'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 6.) First Input All False, Second Input Oscillating between false and true
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0006'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 7.) First Input All False, Second Input Oscillating between true and false
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0007'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 8.) First Input Oscillating between false and true, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0008'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 9.) First Input Oscillating between true and false, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0009'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 10.) First Input Oscillating between false and true, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0010'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 11.) First Input Oscillating between true and false, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0011'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 12.) First Input Five Time Step Pulse Wave, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0012'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 13.) First Input Five Time Step Pulse Wave, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0013'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 14.) First Input Five Time Step Pulse Wave, Second Input All True
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0014'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 15.) First Input Five Time Step Pulse Wave, Second Input All False
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0015'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 16.) First Input All True, Second Input Five Time Step Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0016'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 17.) First Input All False, Second Input Five Time Step Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0017'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 18.) First Input All True, Second Input Five Time Step Inverse Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0018'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 19.) First Input All False, Second Input Five Time Step Inverse Pulse Wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0019'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 20.) Both Inputs are 5 time step pulse waves
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0020'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 21.) First Input 5 time step Inverse Pulse Wave. Second Input 5 time step pulse wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0021'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 22.) First Input 5 time step Inverse Pulse Wave. Second Input 5 time step pulse wave
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0022'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 23.) Both Inputs are 5 time step pulse waves
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0023'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 24.) Both Inputs are five time step pulses, with the second input shifted right by 3
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0024'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 25.)  Both Inputs are five time step pulses, with the second input shifted right by 3
    #       First Input Wave is inverse wave.
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0025'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 26.)  Both Inputs are five time step pulses, with the second input shifted right by 3
    #       Second Wave is Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0026'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 27.) Both Inputs are five time step pulses, with the second input shifted right by 3
    #      First and second waves are Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0027'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 28.) Both Inputs are five time step pulses, with the first input shifted right by 3
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0028'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 29.)  Both Inputs are five time step pulses, with the first input shifted right by 3
    #       Scond Input Wave is inverse wave.
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0029'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 30.)  Both Inputs are five time step pulses, with the first input shifted right by 3
    #       First Wave is Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0030'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 31.) Both Inputs are five time step pulses, with the second input shifted right by 3
    #      First and second waves are Inverse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0031'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 32.) Figure 4.39
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0032'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 33.) Example for TACAS14 Paper
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0033'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 34.) test AND operation
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0034'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 35.) First Input all True; Second Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0035'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 36.) First Input all True; Second Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0036'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 37.) First Input all True; Second Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0037'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 38.) First Input all True; Second Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0038'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 39.) Second Input all True; First Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0039'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 40.) Second Input all True; First Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0040'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 41.) Second Input all True; First Input Increasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0041'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 42.) Second Input all True; First Input Increasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0042'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 43.) First Input all True; Second Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0043'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 44.) First Input all True; Second Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0044'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 45.) First Input all True; Second Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0045'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 46.) First Input all True; Second Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0046'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 47.) Second Input all True; First Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0047'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 48.) Second Input all True; First Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0048'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 49.) Second Input all True; First Input Decreasing Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0049'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 50.) Second Input all True; First Input Decreasing Inverse Pulse
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0050'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 51.) 
    #------------------------------------------------------------------------------------#
    # Create the file
    filename = 'input0051'
    f = open(__InputDir__ + filename + '.csv','wb')
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
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()
    #------------------------------------------------------------------------------------#
    # 52.) Pei Test Input
    #------------------------------------------------------------------------------------#
    # Create the file
    #filename = 'tacas'
    nRow = 39
    filename = 'input0052'
    f = open(__InputDir__ + filename + '.csv','wb')
    Array = []
    flip = True
    counter = 4
    for i in range(0,nRow):
        Array.append([])
       
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if((i >= 10) and (i <= 24) or (i >= 31)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            # The second input
            elif(j == 1):
                if(((i >= 3) and (i <= 10)) or (i == 13) or ((i >= 15) and (i <= 18)) or ((i >= 21) and (i <= 24)) or ((i >= 26) and (i <= 28)) or (i >= 31)):
                    Array[i].append(1)
                else:
                    Array[i].append(0)
            else:
                Array[i].append(1)

    # Save the array to a .csv file
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()

    #------------------------------------------------------------------------------------#
    # 53.) Pei Test Input
    #------------------------------------------------------------------------------------#
    # Create the file
    nRow = 31
    filename = 'input0053'
    f = open(__InputDir__ + filename + '.csv','wb')
    Array = []
    flip0 = True
    flip1 = True
    counter0 = 1
    counter1 = 4
    for i in range(0,nRow):
        Array.append([])
        # Toggle the input 0
        if(np.mod(i,counter0) == 0):
            flip0 = not flip0
        # Toggle the input 1
        if(np.mod(i,counter1) == 0):
            flip1 = not flip1
        # Double the counter at these times
        if((i == 4) or (i == 12)):
            counter0 = counter0 * 2
        # Half the counter at these time
        if((i == 16) or (i == 24)):
            counter1 = counter1 / 2
        
        for j in range(0,nCol):
            # The first input
            if(j == 0):
                if(flip0):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
            # The second input
            if(j == 1):
                if(flip1):
                    Array[i].append(0)
                else:
                    Array[i].append(1)
    # Save the array to a .csv file
    np.savetxt(f,Array,header=HEADER,fmt="%d",delimiter=",")
    f.close()

#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# If there are no arguements
if len(sys.argv) == 1:
    print("ERROR: Missing input arguement")
    print("Use '-h' flag for more information")
    exit()

# See if inputFiles directory exists; if not make, items
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'

if(not os.path.isdir(__InputDir__)):
    os.mkdir(__InputDir__)

# for removing the formula files
if(sys.argv[1] == '-r'):
    shutil.rmtree(__InputDir__)
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    makeInputs()
    print('Inputs are located in the '+__InputDir__+' directory')
 
else:
    print("Invalid input arguement")
    print("-m to make the formula files")
    print("-r to remove them")  
