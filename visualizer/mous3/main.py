import pathlib
import subprocess
# TODO: Call Script with map, c2p0, and csv files

key_word = "invalid"
runs = 0
sum_fail = 0
var_names=[]
timestep_failures = []
focus_var = []


'''
Import an input file and display a simple graph.
This is for one .out file
'''
# TODO: loop through out files in the desired folder
OUT_DIR = pathlib.Path(".") / "tests" / "tail_to_sun/" 

# pull out variable names from map file
# TODO: Make this file option changable for the user
with open("./tests/tail_to_sun/tts.map", "r") as file:
        for line in file:
            var_names.append(line.split(":")[0])


# Get number of timesetps from one .csv file
with open("./tests/tail_to_sun/traces/tts-0.csv", "r") as file:
    for line in file:
        timestep_failures.append(0)

print(timestep_failures)

# Get variables that are focused on
# TODO: make changable option for users
with open("./tests/tail_to_sun/tts.c2po", "r") as file:

    for line in file:
        if "contract:" in line:
            for word in var_names:
                if word in line:
                    focus_var.append(word)

print(focus_var)




for output in OUT_DIR.glob("*.out"):
    
    #Open File
    with open(output, "r") as file:
        for line in file:
            if key_word in line:
                timestep_failures[int(line[-2])]+= 1
                sum_fail += 1
                
            
        runs += 1


print()
print("TITLE OF FILE WE ARE LOOKING AT")

print()
print("{:13}".format("Time step "), end ="")
time = 0
for i in timestep_failures:
    print("| {}".format(time), end = " ")
    time += 1
print("\n")

for var in var_names:
    if var in focus_var:
        print("\033[43m{:12} |\033[0m".format(var[:12]))
    else:
        print("{:12} |".format(var[:12]))


print("{:12}".format("Num Failures "), end = "")
for i in timestep_failures:
    print("| {}".format(i), end = " ")


print("\n")
print("\033[44mTotal Runs:     {}\033[0m".format(runs))
print("\033[42mTotal Failures: {}\033[0m".format(sum_fail))
print("\033[45mACG Violation:  {}\033[0m".format("PLACEHOLDER"))

        




    
