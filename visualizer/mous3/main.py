import pathlib
import subprocess
# TODO: Call Script with map, c2p0, and csv files

key_word = "invalid"
runs = 0
sum_fail = 0
var_names=[]
timestep_failures = []
fail_file_names = []
focus_var = []
focus_var_index = []



'''
Import an input file and display a simple graph.
This is for one .out file
'''
# TODO: loop through out files in the desired folder
OUT_DIR = pathlib.Path(".") / "tests" / "tail_to_sun/" 

def get_all_var():
    # pull out variable names from map file
    # TODO: Make this file option changable for the user
    with open("./tests/tail_to_sun/tts.map", "r") as file:
            for line in file:
                var_names.append(line.split(":")[0])


def get_no_timestep():
    # Get number of timesetps from one .csv file
    with open("./tests/tail_to_sun/traces/tts-0.csv", "r") as file:
        for line in file:
            timestep_failures.append(0)


def get_focus_var():
    # Get variables that are focused on
    # TODO: make changable option for users
    with open("./tests/tail_to_sun/tts.c2po", "r") as file:

        for line in file:
            if "contract:" in line:
                for word in var_names:
                    if word in line:
                        focus_var.append(word)

        

def get_foc_var_loc():
    i = 0
    for name in var_names:
        if name in focus_var:
            focus_var_index.append(i)
        i += 1

def get_fail_locs(runs, sum_fail):
    for output in OUT_DIR.glob("*.out"):
        outstr =str(output)
        outstr = outstr[-5]
        with open(output, "r") as file:
            for line in file:
                if key_word in line:
                    get_fail_type(outstr, line[-2])
                    timestep_failures[int(line[-2])]+= 1
                    fail_file_names.append(output)
                    sum_fail += 1
            runs += 1
    return runs, sum_fail

def get_fail_type(outstr, fail_loc):
    # print(outstr)
    # print(fail_loc)
    for csv in OUT_DIR.glob("traces/*.csv"):
         if outstr in str(csv):
            with open(csv, "r") as file:
                # get time step of failure
                file = file.readlines()[1:]
                for i in range(len(focus_var_index)):
                    pass
                    # get values of agc violation variables
                    # print(file[int(fail_loc)].replace(",","")[focus_var_index[i]])



                

def display_output():
    print()
    print("TITLE OF FILE WE ARE LOOKING AT")

    print()
    print("{:13}".format("Time step "), end ="")
    time = 0
    for i in timestep_failures:

        if i != 0:
            print("|\033[41m {} \033[0m".format(time), end = "")
        else:
            print("| {} ".format(time), end = "")
        time += 1
    print("\n")

    var_count = 0
    for var in var_names:
        if var in focus_var:
            print("\033[43m{:12} |".format(var[:12]), end = " ")
            for i in range(0, len(timestep_failures)):             
                if timestep_failures[i] != 0:
                    # print(i, end='')
                    print("X | ", end = "")
                else:
                    print("  | ", end = "")
            print("\033[0m")
        else:
            print("{:12} |".format(var[:12]), end = '')
            for i in range(0, len(timestep_failures)):             
                if timestep_failures[i] != 0:
                    print("\033[41m   \033[0m|", end = "")
                else:
                    print("   |", end = "")
            print()

        var_count += 1

    print() 
    print("{:12}".format("Num Failures "), end = "")
    for i in timestep_failures:             
        if i != 0:
            print("|\033[41m {} \033[0m".format(i), end = "")
        else:
            print("| {} ".format(i), end = "")
    print()

        



    print("\n")
    print("\033[44mTotal Runs:     {}\033[0m".format(runs))
    print("\033[42mTotal Failures: {}\033[0m".format(sum_fail))
    print("\033[45mACG Violation:  {}\033[0m".format("PLACEHOLDER"))


if __name__ == "__main__":

    get_all_var()
    get_no_timestep()
    get_focus_var()
    get_foc_var_loc()
    runs, sum_fail = get_fail_locs(runs, sum_fail)
    display_output()





    # print(fail_file_names)

    # pull out [x][y] values for failure locations
    # failure locations determined by focus variable location and non-0 index of fail timestep
    # for each .csv file  
    #     pull out the time-variable value from the 2d array 
    #     Put it in new 2d-array?

    

            




        
