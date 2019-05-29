from MLTL_Compiler import *
import sys


def main():
	#MLTL = "G[1,3](G[2]a0) & G[2]a0 &(a1 U[2] -a0)" 
	MLTL = sys.argv[1]
	parser.parse(MLTL)
	MLTLparse.optimize() # Comment this line to see unoptimized code
	MLTLparse.gen_assembly()
	print(MLTLparse.queue_size_assign())


if __name__ == "__main__":
	main()