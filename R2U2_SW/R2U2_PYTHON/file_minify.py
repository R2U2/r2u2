import os, csv, sys

# This program will take a CSV file as a command_line input and will 
# return an output file with zero-order-holds replacing repeated values

def minify(arg):
    
    # Holds the final values for each row
    row_values = []

    # Open the CSV file specified in the command line
    #with open(arg, newline="") as csvfile:
    with open(arg,'rU') as csvfile:
        csv_reader = csv.reader(csvfile)
        
        # Holds the value of the last line from the file
        last_values = []
        
        
        for row in csv_reader:
        
            # Boolean value that is true when current row inputs are identical to the last row
            duplicate = True
        
            # The current values that are read in from the old file
            current_values = []
            
            # The new values that will be written to the new file
            new_values = []
            
            # Populates the current and new values arrays with the values from the old file
            for item in row:
                current_values.append(item)
                new_values.append(item)
            
            # If last_values is empty, we are on the header row which should not be checked
            if not len(last_values) == 0:
                for index in range(len(new_values)):
                    # Ignores the timestep entry
                    if not index == 0:
                        if (current_values[index] == last_values[index]):
                            new_values[index] = " "
                        elif duplicate == True:
                            duplicate = False
            
            # If the row is not a duplicate of the last or is the header line, it should be included in the new file			
            if not duplicate or len(last_values) == 0:
                row_values.append(new_values)	
                
            # Sets the last line equal to current line read in from the file
            last_values = current_values

    # Creates the new output file name
    file_name = arg.replace(".csv", "_min.csv")

    #storage of output in different directory
    
    
    # Writes the new values to a CSV file called "output.csv"
    with open(file_name, "w") as csvfile:
        csv_writer = csv.writer(csvfile, delimiter=",")
        for row in row_values:
            csv_writer.writerow(row)
    
    csvfile.close()

    #os.chdir('..')
    

if __name__=="__main__":
    minify(sys.argv[1])

#minify('test_four.csv')