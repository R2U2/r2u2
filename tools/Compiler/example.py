from MLTL_Compiler import *


def main():
	#MLTL = "G[1,3](G[2]a0) & G[2]a0 &(a1 U[2] -a0)" 
	MLTL = "a0&a1"
	parser.parse(MLTL)
	MLTLparse.optimize() # Comment this line to see unoptimized code
	MLTLparse.gen_assembly()


if __name__ == "__main__":
	main()