from MLTL_Compiler import *
import sys
import os
import subprocess

def main():
    #MLTL = "G[1,3](G[2]a0) & G[2]a0 &(a1 U[2] !a0)"
    MLTL = sys.argv[1]
    FT = ""
    PT = ""
    
    # Split the PT and FT
    for line in MLTL.split(';'):
        # Ignore lines that are blank
        if(line == ""):
            break
        # Iterate through the line and determine if it is FT or PT
        isFT = 0
        isPT = 0
        for p in line:
            # Determine if the line contains a FT oeprator
            if((p == 'G') or (p == 'F') or (p == 'U') or (p == 'R')):
                isFT = isFT + 1
            # Determine if the line contrains a PT operator
            elif((p == 'Y') or (p == 'H') or (p == 'O') or (p == 'S')):
                isPT = isPT + 1
                
        # If a formula has both PT and FT, throw an error and exit the program
        if((isPT > 0) and (isFT > 0)):
            print('Formula has both past-time and future-time operators.')
            print('R2U2 does not support mixed-time formulas.')
            print('The following formula is invalid: ' + line)
        # Else, if a formula is just past-time,   
        elif((isPT > 0) and (isFT == 0)):
            # Put it in the PT list, for the PT call of postgraph
            PT = PT + line + ';'
        # Else, if the formula is future-time or just propositional logic,
        elif((isPT == 0) and (isFT >= 0)):
            # Put it in the FT list, for the FT call of postgraph
            FT = FT + line + ';'
    
    # Call Postgraph for both sets of formulas, Past-Time (PT) and Future-Time (FT)
    subprocess.run(['python3', 'Compiler/main.py', FT, 'ft'])
    subprocess.run(['python3', 'Compiler/main.py', PT, 'pt'])
    

if __name__ == "__main__":
    main()