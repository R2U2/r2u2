# Hanna Stec 
#Trace File Format Validation 
import csv 

with open("input.csv") as csvfile:
    reader = csv.reader(csvfile)
    data = [r for r in reader]
    
    # tests if the first character in the header names is either a letter or _
    for column in range(len(data[0])):
        # assigns the first character to the variable char
        title = data[0][column]
        char = title[0]
        # tests the first character in the column name
        if char == "_":
            pass
        elif char.isalpha(): 
            pass
        else:
            print("Invalid header name")

    # tests the first column header 
    if data[0][0] == "clock" or data[0][0] == "Clock":
        # tests the column headers after testing the first column header for invalid names
        for column in range(len(data[0])-1):
            
            if data[0][column+1] == "F" :
                print("Invalid header name") 
            elif data[0][column+1] == "G":
                print("Invalid header name") 
            elif data[0][column+1] == "U":
                print("Invalid header name") 
            elif data[0][column+1] == "R":
                print("Invalid header name") 
            elif data[0][column+1] == "Clock" or data[0][column+1] == "clock":
                print("Invalid header name") 
            elif data [0][column+1] == "verdict" or data[0][column+1] == "Verdict":
                print("Invalid header name") 
            elif data [0][column+1] == "Resolved_Time" or data[0][column+1] == "resolved_time":
                print("Invalid header name")  
            else:
                pass
    else:
      print("Invalid header name") 
      
    
    print(data)
     
    
    
    
    
