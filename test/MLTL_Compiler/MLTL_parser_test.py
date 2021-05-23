from MLTL_Compiler import *
import os, glob

# Moves to the directory containing the random MLTL files to test
dir_in = "random_MLTL"
os.chdir(dir_in)

print("The script will test parsing files from " + os.getcwd())

# Create an empty tracefile array to hold the files from the directory
tracefile = []

# Create a counter to determine how many statements were parsed successfully
counter = 0

# Append the file names to the tracefile array
for file in glob.glob("*.mltl"):
    tracefile.append(file)

# Iterate through ever file named in the tracefile
for i in range(len(tracefile)):

    # Open each file in read mode
    with open(tracefile[i], "r") as file:
        # Read the contents of the MLTL file
        formula = file.read().rstrip() + ";"
        print(formula)

    # Close the file
    file.close()

    # Try to parse the MLTL instructions with the Postgraph function
    try:
        Postgraph(MLTL=formula, FTorPT="ft", AT="", optimize_cse=True)

    # If an exception is thrown, then the instructions were not valid to the parser
    except Exception as ex:
        print("An exception occured in test " + str(i))
        print(ex)

    # If no exceptions are thrown, then the instructions were valid
    else:
        print("Test " + str(i) + " passed successfully\n")
        counter = counter + 1


print(str(counter) + " out of " + str(len(tracefile)) + " statements were parsed successfully")

if counter != 100:
    raise RuntimeError(str(100-counter) + " tests failed")
