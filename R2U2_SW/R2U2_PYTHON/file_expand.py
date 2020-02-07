#file expansion script
#expands atomic trace format to fill repeated data points

import csv

#user file input request
file_in = input("Please input the name of the desired csv file, without the extension: ")
file_inx = file_in + ".csv"
print("Input atomic trace file: " + file_inx)

#open atomic trace for reading
with open(file_inx) as csvfile:
  csv_reader = csv.reader(csvfile,delimiter=',')
  #open blank file for writing of expanded format
  f = open(file_in + "_exp.csv","w")
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
      #tests for data represented by empty string or 1, 2, or 3 spaces
	    if row[i] == " " or row[i] == "  " or row[i] == "   " or row[i] == "":
        #replaces empties with data from previous line
	      row[i] = stor[line_count][i]
	  #endfor
    #adds row to storage list
    stor.append(row)
    line_count += 1
  #endfor

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