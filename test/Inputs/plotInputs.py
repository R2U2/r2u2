#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 7th, 2020
# File Name:   plotInputs.py
# Description: A Python 3 script to generate plots of the inputs, to check for their
#              correctness. Also saves them as a .png
#------------------------------------------------------------------------------------#
import matplotlib.pyplot as plt
import numpy as np
import sys
import os

nRow = 32
nCol = 2
numInputs = 53
def plotInputs():
    global nRow,nCol,numInputs
    #------------------------------------------------------------------------------------#
    # Plot each of the inputs from 'input00xx.csv'
    #------------------------------------------------------------------------------------#
    for k in range(0,numInputs):
        # Get the correct filename
        if(k < 10):
            filename = 'input000' + str(k)
        else:
            filename = 'input00' + str(k)
        
        # Open the file and parse the inputs
        f = open('inputFiles/' + filename,'r').read()
        lines = f.split('\n')
        input = []
        for i in range(0,nCol):
            input.append([])
            for line in lines:
                try:
                    input[i].append(float(line.split(',')[i]))
                except:
                    pass
        time = []
        for t in range(0,len(input[0])):
            time.append(t)
        # Graph the output
        f, axarr = plt.subplots(nrows=nCol, ncols=1, figsize = (16,8))
        for i in range(0,nCol):
            axarr[i].step(time, input[i], where = 'post',lw = 3.0)
            axarr[i].set_xlabel('Time', fontsize = 20)
            axarr[i].set_yticks([1,0])
            axarr[i].set_ylim([-0.2,1.2])
            axarr[i].tick_params(axis = 'x', labelsize = 16)
            axarr[i].tick_params(axis = 'y', labelsize = 16)
            axarr[i].set_title('Input ' + str(i), fontsize = 20)
            axarr[i].grid()

        plt.tight_layout()
        plt.savefig('inputImages/'+filename+'.png')
        
        plt.close()

#------------------------------------------------------------------------------------#
# Method for removing formula files
#------------------------------------------------------------------------------------#
def removePlots():
    global numInputs
    for i in range(0,numInputs):
        # Format the filename of the input file name with the correct number of 0s
        if(i < 10):
            inputFilename = "input000" + str(i)
        else:
            inputFilename = "input00" + str(i)
            
        filename = "inputImages/" + inputFilename + '.png'
        try:
            os.remove(filename)
        except:
            pass

#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# for removing the formula files
if(sys.argv[1] == '-r'):
    removePlots()
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    plotInputs()
 
else:
    print("Invalid input arguement")
    print("-m to make the formula files")
    print("-r to remove them")  