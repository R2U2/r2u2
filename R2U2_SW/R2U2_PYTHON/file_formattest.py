#file format test script
#validates trace files contained in a directory

import csv, os, glob
from file_expand import expand
from file_minify import minify

#user input request for desired directory name
#is this always included in current working directory?
dir_in = input("Please input the name of the desired directory: ")
print("The script will use the directory: " + dir_in)

#currently, dir_in must be in the R2U2_PYTHON directory to be functional
os.chdir(dir_in)

#prints test case options
print('Test Cases: \r')
print('1. Expand \r')
print('2. Minify \r')
print('3. Expand-Minify-Expand \r')
print('4. Minify-Expand-Minify \r')

#requests input of desired test case
case = input('Choose a case by indicating its number: ')

#empty array for file name storage
tracefile = []

for file in glob.glob("*.csv"):
    tracefile.append(file)

#expansion only case
if case == '1':
    for i in range(len(tracefile)):
        expand(tracefile[i])
        #tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
    #endfor
elif case == '2':
    for i in range(len(tracefile)):
        minify(tracefile[i])
        #tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
    #endfor
elif case == '3':
    for i in range(len(tracefile)):
        expand(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
        minify(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_min.csv")
        expand(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
    #endfor
elif case == '4':
    for i in range(len(tracefile)):
        minify(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_min.csv")
        expand(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
        minify(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_min.csv")
    #endfor
else:
    print("Invalid case number")
#endif