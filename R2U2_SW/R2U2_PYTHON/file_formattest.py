#file format test script
#validates trace files contained in a directory

import csv, os, glob, shutil
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

#stores csv trace file names in list
for file in glob.glob("*.csv"):
    tracefile.append(file)
#endfor

#directory creation for output storage
pathP = os.getcwd()
path = pathP + '/output'

try:
    os.mkdir(path)
except OSError:
    print ("Directory already exists")
else:
    check = os.getcwd()
    print ("Successfully created output directory: " + check)


#expansion only case
if case == '1':
    for i in range(len(tracefile)):
        expand(tracefile[i])
    #endfor
#minification only case
elif case == '2':
    for i in range(len(tracefile)):
        minify(tracefile[i])
    #endfor
#expansion-minification-expansion case
elif case == '3':
    for i in range(len(tracefile)):
        expand(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
        minify(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_min.csv")
        expand(tracefile[i])
        tracefile[i] = tracefile[i].replace(".csv","_exp.csv")
    #endfor
#minification-expansion-minification case
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

tracefileNew = []

#generates new array of trace files in directory
for file in glob.glob("*.csv"):
    tracefileNew.append(file)
#endfor

#moves output files to output directory
for j in range(len(tracefileNew)):
    if "exp" in tracefileNew[j] or "min" in tracefileNew[j]:
        shutil.move(pathP + '/' + tracefileNew[j],pathP + '/output/' + tracefileNew[j])
    #endif
#endfor