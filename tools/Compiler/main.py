from MLTL_Compiler import *
import sys


def main():
    #MLTL = "G[1,3](G[2]a0) & G[2]a0 &(a1 U[2] !a0)"
    MLTL = sys.argv[1]
    FTorPT = sys.argv[2]
    print(sys.argv[1])
    Postgraph(MLTL,FTorPT,optimize_cse=True)

if __name__ == "__main__":
    main()
