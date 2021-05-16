# Programmer: Zach Lewis
# Date: July 6, 2020
# Project: R2U2 
# File: run_test.py
# Description: Used to run automatically generate files needed for testing, and run the specified testing file

import os, sys, subprocess

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__TestDir__ = __AbsolutePath__ + "../test/"
__InputsDir__ = __TestDir__ + "Inputs/"
__OracleDir__ = __TestDir__ + "Oracle/"
__FormulaDir__ = __TestDir__ + "TL_formula/"



def r2u2test(args):
    
    # Check if input files have been generated
    os.chdir(__InputsDir__)
    if not os.path.isdir("inputFiles"):
        subprocess.run(["python3", __InputsDir__+"genInputs.py","-m"])
    # Check if formula files have been generated
    os.chdir(__FormulaDir__)
    if not os.path.isdir("formulaFiles"):
        subprocess.run(["python3", __FormulaDir__+"genFormulas.py", "-m"])
    # Check if oracle files have been generated
    os.chdir(__OracleDir__)
    if not os.path.isdir("oracleFiles"):
        subprocess.run(["python3", __OracleDir__+"genOracle.py", "-m"])

    if args.version not in ['c', 'cpp', 'python']:
        print("Please enter a valid version of R2U2")
        print("The valid versions are: 'c', 'cpp', 'python'")
        exit()

    if args.subset == "Hydra":
        subprocess.run(["python3", __TestDir__+"HydraSubset.py","-v",args.version], cwd=__TestDir__)
    elif args.subset == "LargePt":
        subprocess.run(["python3", __TestDir__+"LargePtSubset.py","-v",args.version], cwd=__TestDir__)
    elif args.subset == "LargeFt":
        subprocess.run(["python3", __TestDir__+"LargeFtSubset.py","-v",args.version], cwd=__TestDir__)
    elif args.subset == "OldFtSuite":
        subprocess.run(["python3", __TestDir__+"OldFtSuiteSubset.py","-v",args.version], cwd=__TestDir__)
    else:
        print("Please enter a valid testing subset")
        print("The valid subsets are: 'Hydra', 'LargePt', 'LargeFt', 'OldFtSuite'")
        exit()
    

    

