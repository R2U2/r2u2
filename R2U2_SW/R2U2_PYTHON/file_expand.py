import csv
#import array as arr
#max is number of elements per row

with open('example.csv') as csvfile:
    csv_reader = csv.reader(csv_file,delimiter=',')
    line_count = 0
    for row in csv_reader:
        for i in range(max):
	    if row[i]='  ':
	        row[i]=rowold[line_count][i]
	    #endif
	#endfor
	rowold.append(row)
        line_count += 1
    #endfor
