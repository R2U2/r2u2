#Alec Rosentrater
#Event List <-> R2U2 trace 
#Takes an event list csv and returns an R2U2 trace csv

#Import Statements
import numpy as np

import csv
import sys

#ARGS: infilename, trace expansion option, full trace saving configuration
def readargs():
    if len(sys.argv) != 4 and len(sys.argv) != 5:
        print("Incorrect Args: Filename, trace expansion, trace saving configuration")
        print(len(sys.argv))
        exit(0)
    infilename = sys.argv[1]
    stutter_status = int(sys.argv[2])
    if sys.argv[3] == "1":
        save_config = True
    else:
        save_config = False
    #save_config = bool(sys.argv[3])
    if len(sys.argv) == 5:
        outfilename = sys.argv[4]
    else: 
        outfilename == ""
    return(infilename,stutter_status,save_config,outfilename)

if __name__ == "__main__":
    [infilename,stutter_status,save_config,outfilename] = readargs()
    

    #Read the csv into an array

    with open(infilename) as fp:
        reader = csv.reader(fp, delimiter=",", quotechar='"')
        #next(reader, None)  #This line skips the header. Don't skip the header since it tells you how many propositions you have.
        data_read = [row for row in reader]

    header = data_read.pop(0)   #Remove the header after it's read the maximum width of the CSV
    trace = np.array(data_read)



    #Set the minimum event separation
    #minSep = 0

    j = 0
    #print(trace[0])
    while j < len(trace)-1:
        # Loops through each line of data

        #If the current row isn't fully populated, need to fill in the missing values with values from previous timestep
        while '' in trace[j]: #For each empty field in the row
            l = list(trace[j]).index('') #Get its index
            trace[j][l] = trace[j-1][l] #Replace the empty field with its value from the previous row


        event1 = trace[j][0]
        time1 = event1.replace("@","")
        event2 = trace[j+1][0]
        time2 = event2.replace("@","")

        first = float(time1)
        second = float(time2)
        delta = second - first
        ntimes = 0
        if stutter_status !=0:
            ntimes = round((delta) / stutter_status) - 1

        #print("Delta: ",delta)
        #if delta is greater than 1, need to add an agregation alignment event at second-1
        if (delta > 1) and (stutter_status == 0):
            #print("Alignment Needed: Inserting event at ",second-1)
            row = np.copy(trace[(j)])
            row[0] = "@" + str( second-1)
            #print("Inserting row:",row)
            trace = np.insert(trace,(j)+1, row, axis=0)

        #loop n times and fill in the stuttered data
        if(stutter_status):
            for i in range(0,ntimes):
                row = np.copy(trace[(i+j)])
                row[0] = "@" + str(float(row[0].replace("@","")) + stutter_status)
                trace = np.insert(trace,(j+i) + 1, row, axis=0)

        #line by line printing here
        if( not save_config):
            for i in range(j,j+ntimes+1):
                for i,el in enumerate(trace[i]):
                    print(el,end="")
                    if i == 0:
                        print("",end=" ")
                    elif i != len(trace[i])-1:
                        print(",",end=" ")
                print("")

        #compute the next index
        j = j + ntimes +1

    #Print the last frame in the trace
    #print(trace[-1])
    if( not save_config):
        for i,el in enumerate(trace[-1]):
            print(el,end="")
            if i == 0:
                print("",end=" ")
            elif i != len(trace[-1])-1:
                print(",",end=" ")
        print("")
        
    # print("End Main Loop")
    if(save_config and outfilename):
        print("Saving to", outfilename)
        with open(outfilename, 'w') as f:
            print(header, file=f) #Print the header
            #print the result
            for row in trace:
                for i,el in enumerate(row):
                    print(el, file=f, end="")
                    if i == 0:
                        print("",file=f,end=" ")
                    elif i != len(row)-1:
                        print(",",file=f,end=" ")
                print("",file=f)
            #print(test)
        f.close()
