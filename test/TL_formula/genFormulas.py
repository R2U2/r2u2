#------------------------------------------------------------------------------------#
# Author:      Matt Cauwels
# Date:        April 10th, 2020
# File Name:   genInputs.py
# Description: A Pa1thon 3 script used to generate test formula files for cases used
#              for R2U2 regression testing. Note that this script is built using the 
#              old readme file, "README.md", as a template.
#------------------------------------------------------------------------------------#
import sys
import os

numFormula = 36

#------------------------------------------------------------------------------------#
# Method for making formula files
#------------------------------------------------------------------------------------#
def makeFormulas():
    # test0000 - Test Case will output the Negation of the First Input Wave
    filename = 'formulaFiles/test0000'
    f = open(filename,'w+')
    formula = "!a0"
    f.write(formula)
    f.close()

    # test0001 - Test Case will output the Conjunction of the First and Second Input Wave
    filename = 'formulaFiles/test0001'
    f = open(filename,'w+')
    formula = "(a0 & a1)"
    f.write(formula)
    f.close()

    # test0002 - Test Case will output the invariant of zero steps of the First Input Wave
    filename = 'formulaFiles/test0002'
    f = open(filename,'w+')
    formula = "G[0] (a0)"
    f.write(formula)
    f.close()

    # test0003 - Test Case will output the invariant of 5 time steps of the First Input Wave
    filename = 'formulaFiles/test0003'
    f = open(filename,'w+')
    formula = "G[5] (a0)"
    f.write(formula)
    f.close()

    # test0004 - Test Case will output the invariant of a zero interval of the First Input Wave
    filename = 'formulaFiles/test0004'
    f = open(filename,'w+')
    formula = "G[0,0] (a0)"
    f.write(formula)
    f.close()

    # test0005 - Test Case will output the invariant of 1 interval of the First Input Wave
    filename = 'formulaFiles/test0005'
    f = open(filename,'w+')
    formula = "G[0,1] (a0)"
    f.write(formula)
    f.close()

    # test0006 - Test Case will output the variant of an interval [5,10] of the First Input Wave
    filename = 'formulaFiles/test0006'
    f = open(filename,'w+')
    formula = "G[5,10] (a0)"
    f.write(formula)
    f.close()

    # test0007 - Test Case will output the First Input Wave Until an interval an zero interval, the Second Input Wave
    filename = 'formulaFiles/test0007'
    f = open(filename,'w+')
    formula = "(a0) U[0,0] (a1)"
    f.write(formula)
    f.close()

    # test0008 - Test Case will output the First Input Wave Until an interval of 1, the Second Input Wave
    filename = 'formulaFiles/test0008'
    f = open(filename,'w+')
    formula = "(a0) U[0,1] (a1)"
    f.write(formula)
    f.close()

    # test0009 - Test Case will output the First Input Wave Until an interval of [5,10], the Second Input Wave
    filename = 'formulaFiles/test0009'
    f = open(filename,'w+')
    formula = "(a0) U[5,10] (a1)"
    f.write(formula)
    f.close()

    # test0010 - Test Case will output the First Input Wave Until an interval of [0,2], the Second Input Wave
    filename = 'formulaFiles/test0010'
    f = open(filename,'w+')
    formula = "(a0) U[0,2] (a1)"
    f.write(formula)
    f.close()

    # test0011
    #  - Test Case representing TACAS_ea0amples
    #  - Test Case will output Altitude and Pitch Signals
    #  - Test Case Negation will output !(Pitch)
    #  - Test Case InvarNea0tTsteps will output G[5] (Pitch)
    #  - Test Case InvarFutInterval will output G[5,10] (Altitude)
    #  - Test Case Conjunction will output (Altitude & Pitch)
    #  - Test Case Until will output Pitch U[5,10]  Altitude
    #  - Test Case ConjunctionwithInvarNea0tTsteps will output (Pitch & G[5] (Altitude))

    # test0012 - Test Case will output the First Input Wave Until an interval of [1,2], the Second Input Wave
    filename = 'formulaFiles/test0012'
    f = open(filename,'w+')
    formula = "(a0) U[1,2] (a1)"
    f.write(formula)
    f.close()

    # test0013 - Test Case will output the First Input Wave Until an interval of [2,3], the Second Input Wave
    filename = 'formulaFiles/test0013'
    f = open(filename,'w+')
    formula = "(a0) U[2,3] (a1)"
    f.write(formula)
    f.close()

    # test0014 - Test Case will output AND result with two input under different time stamps
    filename = 'formulaFiles/test0014'
    f = open(filename,'w+')
    formula = "a0 & G[2] (a1)"
    f.write(formula)
    f.close()

    # test0015 - Test Case will test AND operation combined with NOT
    filename = 'formulaFiles/test0015'
    f = open(filename,'w+')
    formula = "(!a1) & (a0)"
    f.write(formula)
    f.close()

    # test0016 - Test Case testing embedding AND operations
    filename = 'formulaFiles/test0016'
    f = open(filename,'w+')
    formula = "(a0 & a0) & (a1)"
    f.write(formula)
    f.close()

    # test0017 - Test Case testing embedding NOT operations and AND
    filename = 'formulaFiles/test0017'
    f = open(filename,'w+')
    formula = "(!(!a0)) & (a1)"
    f.write(formula)
    f.close()

    # test0018 - Test Case testing negation of a value that should alwaa1s be true
    filename = 'formulaFiles/test0018'
    f = open(filename,'w+')
    formula = "!(a0 & a0)"
    f.write(formula)
    f.close()

    # test0019 - Test Case testing interval operation with an input that should alwaa1s be true
    filename = 'formulaFiles/test0019'
    f = open(filename,'w+')
    formula = "G[5] (a0 & a0)"
    f.write(formula)
    f.close()

    # test0020 - Test Case testing interval operation with an input that should alwaa1s be true with added negations
    filename = 'formulaFiles/test0020'
    f = open(filename,'w+')
    formula = "G[5] (!(!(a0 & a0)))"
    f.write(formula)
    f.close()

    # test0021 - Test Case testing negation of an future time operation
    filename = 'formulaFiles/test0021'
    f = open(filename,'w+')
    formula = "!(G[2] a0)"
    f.write(formula)
    f.close()

    # test0022 - Test Case testing conjunction of two future time operations
    filename = 'formulaFiles/test0022'
    f = open(filename,'w+')
    formula = "(G[2] a0) & (G[2] a1)"
    f.write(formula)
    f.close()

    # test0023 - Test Case testing double negation
    filename = 'formulaFiles/test0023'
    f = open(filename,'w+')
    formula = "!(!a0) "
    f.write(formula)
    f.close()

    # test0024 - Test Case testing global interval 5 steps of 2nd input
    filename = 'formulaFiles/test0024'
    f = open(filename,'w+')
    formula = "G[5] a1"
    f.write(formula)
    f.close()

    # test0025 - Test Case testing negation of interval of negated input
    filename = 'formulaFiles/test0025'
    f = open(filename,'w+')
    formula = "!(G[2] (!a1) )"
    f.write(formula)
    f.close()

    # test0026 - Test Case testing combination of conjunction with interval
    filename = 'formulaFiles/test0026'
    f = open(filename,'w+')
    formula = "(G[2] a0) & (a1)"
    f.write(formula)
    f.close()

    # test0027 - Test Case testing negation of conjunction of two different ta1pes of interval operations
    filename = 'formulaFiles/test0027'
    f = open(filename,'w+')
    formula = "!( (G[5,10] a0) & (G[2] a1) ))"
    f.write(formula)
    f.close()

    # test0028 - Test Case testing double negation of interval and conjunction testing
    filename = 'formulaFiles/test0028'
    f = open(filename,'w+')
    formula = "G[2](!(!a0)) & a1"
    f.write(formula)
    f.close()

    # test0029 - Test Case testing Conjunction with future interval
    filename = 'formulaFiles/test0029'
    f = open(filename,'w+')
    formula = "a1 & (G[0,8] a0)"
    f.write(formula)
    f.close()

    # test0030 - Test Case testing Conjunction of different interval operations
    filename = 'formulaFiles/test0030'
    f = open(filename,'w+')
    formula = "(G[2] a1) & (G[5,10] a0)"
    f.write(formula)
    f.close()

    # test0031 - Test Case testing interval of 2nd input
    filename = 'formulaFiles/test0031'
    f = open(filename,'w+')
    formula = "G[2] a1"
    f.write(formula)
    f.close()

    # test0032 - Test Case testing multiple conjunctions with intervals
    filename = 'formulaFiles/test0032'
    f = open(filename,'w+')
    formula = "(a0 & a1) & (G[3,5] a0)"
    f.write(formula)
    f.close()

    # test0034 - Test Case testing multiple conjunctions with intervals
    filename = 'formulaFiles/test0034'
    f = open(filename,'w+')
    formula = "a1 & F[5,10] a0"
    f.write(formula)
    f.close()

    # test0035 - Test Case testing for complea0 global
    filename = 'formulaFiles/test0035'
    f = open(filename,'w+')
    formula = "G[2,4](G[2]a1)"
    f.write(formula)
    f.close()
    
#------------------------------------------------------------------------------------#
# Method for removing formula files
#------------------------------------------------------------------------------------#
def removeFormulas():
    global numFormula
    for i in range(0,numFormula):
        # Format the filename of the input file name with the correct number of 0s
        if(i < 10):
            formulaFilename = "test000" + str(i)
        else:
            formulaFilename = "test00" + str(i)
            
        filename = "formulaFiles/" + formulaFilename
        try:
            os.remove(filename)
        except:
            pass

#------------------------------------------------------------------------------------#
# Main function call
#------------------------------------------------------------------------------------#
# for removing the formula files
if(sys.argv[1] == '-r'):
    removeFormulas()
            
# for generating the formula files
elif(sys.argv[1] == '-m'):
    makeFormulas()
 
else:
    print("Invalid input arguement")
    print("-m to make the formula files")
    print("-r to remove them")  