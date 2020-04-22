from MLTL_Compiler import *

def main():
    formula = '''
    G[1,3](G[2]a0) & G[2]a0 &(a1 U[2] !a0);
    a0 U[2,3] f3;
    Y a0;
    O[3,5]a0 & b2;
    O[2] a0;
    a0 -> b;
    a0 <->a1;
    True;
    true;
    true & false;
    '''
    pg = Postgraph(MLTL=formula,optimize_cse=True)


if __name__ == "__main__":
    main()