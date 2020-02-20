#file expansion script
#expands atomic trace format to fill repeated data points

import os,csv

def expand(file_input):
  #open atomic trace for reading
  #file_inx = file_input + ".csv"
  with open(file_input,'rU') as csvfile:
    csv_reader = csv.reader(csvfile,delimiter=',')
    #open blank file for writing of expanded format
  
    line_count = 0
  
    #finds number of columns and reset to reader to first row
    col=len(next(csv_reader)) 
    csvfile.seek(0)   

    #create 2D list for storing data
    #begins with row of zeros, which is not printed to file
    stor = [[0] * col for i in range(1)] 

    #reads data and replaces blank points with previous data
    for row in csv_reader:
      for i in range(col):
        #tests for data represented by empty string or space(s)
        if row[i].isspace() or not row[i]:
          #replaces empties with data from previous line
          row[i] = stor[line_count][i]
        #endif
      #endfor
      #adds row to storage list
      stor.append(row)
      line_count += 1
    #endfor
    
    file_in = file_input.replace(".csv","_exp.csv")
    f = open(file_in,"w")
    #writes storage array to expanded file
    for j in range(line_count+1):
      for k in range(col):
        if j != 0:
          if k == col-1:
            f.write(str(stor[j][k]))
          else:
            f.write(str(stor[j][k]) + ',')
          #endif
        #endif
      #endfor
      if j != line_count and j != 0:
        f.write('\r')
      #endif
    #endfor  

    #closes read and write files
    csvfile.close() 
    f.close()

  
#user file input request (currently non-functional)
'''file_in = input("Please input the name of the desired csv file in quotes, without the extension: ")
file_inx = file_in + ".csv"
print("Input atomic trace file: " + file_inx)
'''
#expand('test_four.csv')