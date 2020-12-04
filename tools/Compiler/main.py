from MLTL_Compiler import *
import sys
from ATcompiler import AT

def main():
    #MLTL = "G[1,3](G[2]a0) & G[2]a0 &(a1 U[2] !a0)"
    MLTL = sys.argv[1]
    FTorPTorAT = sys.argv[2]
    at = sys.argv[3]
    if FTorPTorAT == 'at':
        AT(at)
    else:
        Postgraph(MLTL,FTorPTorAT,at,optimize_cse=True)

if __name__ == "__main__":
    main()
