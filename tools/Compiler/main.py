from MLTL_Compiler import *
import sys


def main():
    formula = "((! (alpha))) & ((F[93,98](beta)));"
    ftpt = "ft"
    #MLTL = sys.argv[1]
    #FTorPT = sys.argv[2]
    Postgraph(MLTL=formula,FTorPT="ft",optimize_cse=True)

if __name__ == "__main__":
    main()
