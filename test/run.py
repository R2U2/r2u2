import os
import argparse
import subprocess
import re
from subprocess import check_output

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))
__TLDir__ = __AbsolutePath__+'/TL_formula/'
__InputDir__ = __AbsolutePath__+'/Inputs/'
__PythonDir__ = __AbsolutePath__+'/../R2U2_SW/R2U2_PYTHON/'
__CDir__ = __AbsolutePath__+'/../R2U2_SW/R2U2_C/'
__CPPDIR__ = __AbsolutePath__+'/../R2U2_SW/R2U2_CPP/'
__VHDLDIR__ = __AbsolutePath__+'/../R2U2_HW/R2U2_VHDL/'
__ResultDIR__ = __AbsolutePath__+'/results/'
__ToolDir__ = __AbsolutePath__+'/../tools/Compiler/'

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

def post_file_process(file):
	# Reformat the output file
	f=open(file,'r')
	f_temp = open(file+'_tmp','w')
	lines =  [i.strip() for i in f]
	pattern = re.compile(r'(?=PC\=[\d]+:)|([-]{3}RTC:[\d]+[-]{3})')
	PC_pattern = re.compile(r'\s*PC\=[\d]+:\s*')
	for line in lines:
		pc = re.split(pattern,line)
		pc = [x for x in pc if (x and not PC_pattern.fullmatch(x))]
		for y in pc:
			f_temp.write(y+'\n')
	f.close()
	f_temp.close()
	os.rename(file+'_tmp', file)

def test_python(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+'python_version/'
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	for _formula in formulaFiles:
		f = open(__TLDir__+_formula,'r')
		lines =  [i.strip() for i in f]
		for cnt,line in enumerate(lines):
			out = check_output(["python", __ToolDir__+'main.py',line])
			for _input in inputFiles:
				filename = __OutputDIR__+_formula+'_case'+str(cnt)+'.txt'
				subprocess.run(["python", __PythonDir__+'MLTL_main.py','-m',out,'-a',__InputDir__+_input,'-o',filename])
		f.close()
		post_file_process(filename)


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