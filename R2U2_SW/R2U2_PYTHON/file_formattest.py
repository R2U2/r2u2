#file format test script
#validates trace files contained in a directory

import csv, os, glob
from file_expand import expand

#user input request for desired directory name
#is this always included in current working directory?
dir_in = input("Please input the name of the desired directory: ")
print("The script will use the directory: " + dir_in)

#currently, dir_in must be in the R2U2_PYTHON directory to be functional
os.chdir(dir_in)

tracefile = []

for file in glob.glob("*.csv"):
    tracefile.append(file)

#expansion only case

for i in range(len(tracefile)):
    expand(tracefile[i])