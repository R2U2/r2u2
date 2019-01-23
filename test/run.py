import os
import argparse
import subprocess

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))
__TLDir__ = __AbsolutePath__+'/TL_formula/'
__InputDir__ = __AbsolutePath__+'/Inputs/'
__PythonDir__ = __AbsolutePath__+'/../R2U2_SW/R2U2_PYTHON/'
__CDir__ = __AbsolutePath__+'/../R2U2_SW/R2U2_C/'
__CPPDIR__ = __AbsolutePath__+'/../R2U2_SW/R2U2_CPP/'
__VHDLDIR__ = __AbsolutePath__+'/../R2U2_HW/R2U2_VHDL/'
__ResultDIR__ = __AbsolutePath__+'/results/'

def parserInfo():
	parser = argparse.ArgumentParser(description='Suffer from R2U2 Runtime Verification Regression Test')
	parser.add_argument('-v','--version', help='Choose the R2U2 implementation version to test', required=True)
	args = vars(parser.parse_args())
	return args

def list_file():
	from os import listdir
	from os.path import isfile, join
	formulaFiles,inputFiles = [[f for f in listdir(i) if isfile(join(i, f))] for i in (__TLDir__,__InputDir__)]
	print('#MLTL file: '+str(len(formulaFiles))+'\n#Input case: '+str(len(inputFiles)))
	return formulaFiles,inputFiles

def test_python(formulaFiles,inputFiles):
	for _formula in formulaFiles:
		f = open(__TLDir__+_formula,'r')
		lines =  [i.strip() for i in f]
		for line in lines:
			for _input in inputFiles:
				subprocess.run(["python", __PythonDir__+'MLTL_main.py','-m',line,'-a',__InputDir__+_input])
		f.close()


def test_c():
	pass

def test_cpp():
	pass

def test_vhdl():
	pass

def test_board():
	pass

def main():
	args = parserInfo()
	formulaFiles,inputFiles = list_file()
	if(args['version'].lower()=='python'):
		test_python(formulaFiles,inputFiles)
	elif(args['version'].lower()=='c'):
		test_c()
	elif(args['version'].lower()=='cpp'):
		test_cpp()
	elif(args['version'].lower()=='vhdl'):
		test_vhdl()
	elif(args['version'].lower()=='board'):
		test_board()


if __name__ == "__main__":
   main()