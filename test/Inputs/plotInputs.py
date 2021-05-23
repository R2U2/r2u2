#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 7th, 2020
# File Name:   plotInputs.py
# Description: A Python 3 script to generate plots of the inputs, to check for their
#              correctness. Also saves them as a .png
#------------------------------------------------------------------------------------#
import shutil
import matplotlib.pyplot as plt
import numpy as np
import sys
import os
from os import listdir
from os.path import isfile, join

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__InputDir__     = __AbsolutePath__+'inputFiles/'
__PlotDir__      = __AbsolutePath__+'InputImages/'

def plotInputs(inputFiles):
    #------------------------------------------------------------------------------------#
    # Plot each of the inputs from 'input00xx.csv'
    #------------------------------------------------------------------------------------#
    for _inputFile in inputFiles:
        f = open(__InputDir__ + _inputFile,'r').read()
        lines = f.split('\n')
        input = []
        nCol = len(lines[0].split(','))
        for i in range(0,nCol):
            input.append([])
            for line in lines:
                try:
                    input[i].append(float(line.split(',')[i]))
                except EOFError:
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
        filename = _inputFile.replace('.csv','')
        plt.savefig(__PlotDir__+filename+'.png')
        
        plt.close()

#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# If there are no arguements
if len(sys.argv) == 1:
    print("ERROR: Missing input arguement")
    print("Use '-h' flag for more information")
    exit()

# See if inputImages directory exists; if not make, items

if(not os.path.isdir(__PlotDir__)):
    os.mkdir(__PlotDir__)

# for removing the formula files
if(sys.argv[1] == '-r'):
    shutil.rmtree(__PlotDir__)
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    inputFiles = [f for f in listdir(__InputDir__) if isfile(join(__InputDir__, f))]
    plotInputs(inputFiles)
    print('Plots are located in the '+__PlotDir__+' directory')
 
else:
    print("Invalid input arguement")
    print("-m to make the formula files")
    print("-r to remove them")  
