#******************************************************************************#
# Programmer: Matt Cauwels
# Date: July 18th, 2019
# Project: R2U2 - Regression Testing
# File Name: results.py
# Description: Scan through the results files for all versions of R2U2 and
#              compare them against one another. Report if any version 
#              mismatches against the other two. Write the results in a 
#              Report.txt file
#******************************************************************************#
# The maximum number of Groups, Cases, and Formulas
GROUP_LIMIT = 2
CASE_LIMIT = 2
FORMULA_LIMIT = 6

# Initialize the Group, Case, Formula, and Line number
Gnum = 0
Cnum = 0
Fnum = 0
Lnum = 0

# Create the Results.txt
f = open("Results.txt",'w')
# Loop through each of the Groups, cases, and formulas for each file.
for Gnum in range(GROUP_LIMIT):
    for Cnum in range(CASE_LIMIT):
        for Fnum in range(FORMULA_LIMIT):
            # Open each versions file and loop through the lines to see if they're equivalent
            f1 = open("results/c_version/group_" + str(Gnum) + "case_" + str(Cnum) + "formula_" + str(Fnum) + ".txt", 'r')
            f2 = open("results/python_version/group_" + str(Gnum) + "case_" + str(Cnum) + "formula_" + str(Fnum) + ".txt", 'r')
            for line1 in f1:
                for line2 in f2:
                    Lnum = Lnum + 1
                    if line1 != line2:
                        line = "Mismatch between Group"+str(Gnum)+" Case"+str(Cnum)+" Formula"+str(Fnum)+" at line"+str(Lnum)
                        f.write(line + "\n");
                    break
            f1.close();
            f2.close();
            Lnum = 0;
f.close();