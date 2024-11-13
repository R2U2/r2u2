import os, glob

# Converts a folder of files from the MLTL standard to an R2U2 input file
def MLTL_to_R2U2_folder(folder_name):
    # Change directory to the specified folder
    os.chdir(folder_name)

    tracefile = []
    output_values = []

    # For every file in the folder with a ".mltl" extension, add it to the tracefile list
    for file in glob.glob("*.mltl"):
        tracefile.append(file)

    for i in range(len(tracefile)):
        # Open every file listed in the trace file
        output_values.append("")
        with open(tracefile[i], "r") as file:
            for line in file:
                # Use the convert function to change the formula to r2u2 format
                r2u2_formula = convert(line)
                # Add the output of the convert function to the output_values array
                output_values[i] = output_values[i] + r2u2_formula

        file.close()

    # Move to the folder above the current directory, then try to make a new folder and move to it
    os.chdir("..")
    try:
        os.mkdir(folder_name + "_R2U2")
    except Exception:
        pass
    os.chdir(folder_name + "_R2U2")
	
    # Loop through every file in the tracefile
    for i in range(len(tracefile)):
        
        # Create a new file name based on the old file name, but with an "_r2u2" extension
        file_name = tracefile[i].replace(".mltl", "_r2u2")
        
        # Open the file and write the specified output to the file
        with open(file_name, "w") as file:
            file.write(output_values[i])

        file.close()


# Converts a file from the MLTL standard to an R2U2 input file
def MLTL_to_R2U2_file(file_name):

    output_values = []

    # Open the file, and for every line in the file convert it and append it to the output_values array
    with open(file_name) as file:
        for line in file:
            output_values.append(convert(line))

    file.close()

    # Create a new file name with an "_r2u2" extension
    new_file_name = file_name.replace(".mltl", "_r2u2")

    # Add the output_values lines to the new file
    with open(new_file_name, "w") as file:
        for row in output_values:
            file.write(row)

    file.close()


# Converts a given line from MLTL to R2U2 input
def convert(line):

    # Replace all MLTL comparison operators with the equivalent R2U2 operators
    line = line.replace("&&", "&")
    line = line.replace("||", "|")
    line = line.replace("==", "<->")
    
    # Strip the trailing newline character if there is one
    line = line.rstrip("\n")   
    # Add a semicolon at the end of the line, and add a newline character
    line = line + ";\n"    
    
    return line
