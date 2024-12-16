import pathlib
import subprocess
# TODO: Call Script with map, c2p0, and csv files

key_word = "invalid"
runs = 0
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
                
            
        runs += 1

print("Runs: ", runs)
print(timestep_failures)
        



        # print(content)
        #Setup Dataframe
        # meta_data = file.readline().strip().split(',')
        
#BUG: There is no meta data from how script is run right now

        # no_var = int(meta_data[0])
        # no_timestep = int(meta_data[1])

        # var_names = file.readline().strip().split(',')
        # var_names.append("G")
    

        # # Add Number of time steps to columns
        # columns = ['variable']
        # for i in range(no_timestep):
        #     columns.append(i)
        # print(columns)

    #     data = {} 

    #     for i in range(len(var_names)):
    #         data[i] = []
        
    #     data[len(var_names)-1] =[] 
    #     fail_no = []
    #     for line in file:
    #         #save the outputs
    #         if key_word in line:
    #             fail_no.append(int(line.strip().split(' ')[-1]))
    #             # print(fail_no)

    #         if ':' in line:
    #             com_sep = line.strip().split(',')
    #             bool = com_sep[-1]
    #             var_data = com_sep[0].split(':')

    #             var = int(var_data[0])
    #             time = int(var_data[1])

    #             data[var].append(bool)

    # # print(data)
    # space = " "
    # print(f"{space:3s}", end=" ")
    # for i in range(len(data[0])):
    #     print(f"{str(i):3s}", end=" ")

    # print()
    # count = 0
    # var = 0
    # for x in data:
    #     print(f"{var_names[var]:3s}", end=" ")
    #     for y in data[x]:
    #         if count in fail_no:
    #             print(f"\033[31m{y:3s}\033[0m", end=" ")
    #         else:
    #             print(f"{y:3s}", end=" ")
    #         count += 1
    #     print()
    #     count = 0
    #     var += 1
    
