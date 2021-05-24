#------------------------------------------------------------------------------------#
# Author:      Pei Zhang(1st), Matt Cauwels(2nd)
# Date:        April 12th, 2020
# File Name:   run.py
# Description: A Python 3 script used automatically run any version of R2U2, based on
#              the version specified in the input arguement. Output logs of R2U2 can
#              be found in the 'results/XXX_version/' directory, where *** is the 
#              version (c, cpp, vhdl). The results directory can be cleaned by
#              entering the input flag '-r', rather than '-v', and any arguement.
#------------------------------------------------------------------------------------#
import shutil
import os
import argparse
import subprocess
import re
from subprocess import check_output

'''
Paths needed to navigate across the r2u2 directory
'''
__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__TLDir__        = __AbsolutePath__+'TL_formula/formulaFiles/'
__InputDir__     = __AbsolutePath__+'Inputs/inputFiles/'
__CDir__         = __AbsolutePath__+'../R2U2_C/'
__CPPDIR__       = __AbsolutePath__+'../R2U2_CPP/'
__VHDLDIR__      = __AbsolutePath__+'../R2U2_HW/'
__ResultDIR__    = __AbsolutePath__+'results/'
__CompilerDir__  = __AbsolutePath__+'../tools/Compiler/'
__BinGenDir__    = __AbsolutePath__+'../tools/AssemblyToBinary/'

# Names of the directories where the results for each version are stored
__ResultCDir__      = 'c_version/'
__ResultCppDir__    = 'cpp_version/'
__ResultVHDLDir__   = 'vhdl_version/'
'''

'''
def parserInfo():
	parser = argparse.ArgumentParser(description='Suffer from R2U2 Runtime Verification Regression Test')
	parser.add_argument('-v','--version', help='Choose the R2U2 implementation version to test', required=False)
	parser.add_argument('-r','--remove', help='Remove all R2U2 log files from the /results/ directory', required=False)
	args = vars(parser.parse_args())
	return args

'''
Method for listing all the files within a given directory.
'''
def list_file():
	from os import listdir
	from os.path import isfile, join
	formulaFiles,inputFiles = [[f for f in listdir(i) if isfile(join(i, f))] for i in (__TLDir__,__InputDir__)]
	print('#MLTL file: '+str(len(formulaFiles))+'\n#Input case: '+str(len(inputFiles)))
	return formulaFiles,inputFiles

# def post_file_process(file):
# 	# Reformat the output file
# 	f=open(file,'r')
# 	f_temp = open(file+'_tmp','w')
# 	lines =  [i.strip() for i in f]
# 	pattern = re.compile(r'(?=PC\=[\d]+:)|([-]{3}RTC:[\d]+[-]{3})')
# 	PC_pattern = re.compile(r'\s*PC\=[\d]+:\s*')
# 	for line in lines:
# 		pc = re.split(pattern,line)
# 		pc = [x for x in pc if (x and not PC_pattern.fullmatch(x))]
# 		for y in pc:
# 			f_temp.write(y+'\n')
# 	f.close()
# 	f_temp.close()
# 	os.rename(file+'_tmp', file)

'''

'''
def subprocess_cmd(command):
	process = subprocess.Popen(command,stdout=subprocess.PIPE, shell=True)
	proc_stdout = process.communicate()[0].strip()
	print(proc_stdout)

'''

'''
def preprocessVHDLinput(input_case):
	f = open(input_case)
	lines =  [i.strip() for i in f][1:] # remove first line (first line is the atomic name, useless in VHDL test)
	output_case = []
	fw= open(__VHDLDIR__+"ftMuMonitor/sim/testcases/atomic.trc","w+") # location of the trace file for tb.vhd
	for each_atomic in lines:
		fw.write(each_atomic.replace(" ","").replace(",","")+'\n')
	fw.close()
	f.close()

'''
Method for generating the assembly code for R2U2 based on the given MLTL formula.
'''
def gen_assembly(MLTL,timestamp_byte=4,gen_bin=True):
	#print(MLTL)
	subprocess.run(["python3", __CompilerDir__+'main.py',MLTL], stdout=subprocess.PIPE)
	#print("python3 " + __CompilerDir__+'main.py ' + MLTL)
	f = open('tmp.ftasm')
	asm = f.read()
	f.close()
	if gen_bin:
		subprocess.run(["python3", __BinGenDir__+'ftas.py','tmp.ftasm',str(timestamp_byte)], stdout=subprocess.PIPE)
	return asm

'''
Method for testing the C version of R2U2.
Note: You must 'make' the R2U2 file within the R2U2_C directory prior to running this method!
'''
def test_c(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+__ResultCDir__
	# subprocess_cmd('cd '+__CDir__+'; '+'make') # compile C version
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	# For all formula files within the formulaFiles directory
	for _formulaFile in formulaFiles:
		f = open(__TLDir__+_formulaFile,'r')
		lines =  [i.strip() for i in f]
		# For each formula within 
		for cnt,formula in enumerate(lines):
			gen_assembly(formula,4,True)
			for _input in inputFiles:
				formula = _formulaFile.replace('.mltl','')
				trace = _input.replace('.csv','')
				filename = __OutputDIR__+ formula+'_'+trace+'.txt'
				# subprocess.run([__CDir__+'bin/r2u2',__InputDir__+_input,'tmp.ftm','tmp.fti','tmp.ftscq'],stdout=subprocess.PIPE)
				subprocess.run([__CDir__+'bin/r2u2',__InputDir__+_input,'tmp.ftm','tmp.fti','tmp.ftscq'])
				subprocess.run(['mv','R2U2.log',filename],stdout=subprocess.PIPE)
		f.close()
	# Cleanup the tmp assembly R2U2 files
	for tmp in ('tmp.ftasm','tmp.ftm','tmp.fti','tmp.ftscq','R2U2.out'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)

'''
Method for testing the C++ version of R2U2.
'''
def test_cpp(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+__ResultCppDir__
	# subprocess_cmd('cd '+__CPPDIR__+'; '+'make') # compile Cpp version
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	for _formulaFile in formulaFiles:
		f = open(__TLDir__+_formulaFile,'r')
		lines =  [i.strip() for i in f]
		for cnt,formula in enumerate(lines):
			gen_assembly(formula,4,True)
			for _input in inputFiles:
				filename = __OutputDIR__+_formulaFile+_input+'.txt'
				#print(filename)
				subprocess.run([__CPPDIR__+'build/app/MLTL','tmp.ftasm',__InputDir__+_input,"result.txt"])
				#print(__CPPDIR__+'build/app/MLTL')
				# quit()
				subprocess.run(['mv','result.txt',filename],stdout=subprocess.PIPE)
		f.close()
	for tmp in ('tmp.ftasm','tmp.ftm','tmp.fti','tmp.ftscq','result.txt'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)

'''
Method for testing the VHDL version of R2U2.
Note: GHDL must be installed prior to running this method!
'''
def test_vhdl(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+__ResultVHDLDir__
	# subprocess_cmd('cd '+__CDir__+'; '+'make') # compile C version
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	for _formulaFile in formulaFiles:
		f = open(__TLDir__+_formulaFile,'r')
		lines =  [i.strip() for i in f]
		for cnt,formula in enumerate(lines):
			gen_assembly(formula,2,True)
			for tmp in ('tmp.ftm','tmp.fti'):
				subprocess.run(['cp',tmp,__VHDLDIR__+"ftMuMonitor/sim/testcases/"],stdout=subprocess.PIPE)
			# quit()
			for _input in inputFiles:
				preprocessVHDLinput(__InputDir__+_input) # generate trc file
				filename = __OutputDIR__+     _formulaFile+_input+'.txt'
				#print(filename)
				
				subprocess.run(['bash',__VHDLDIR__+'GHDL_scripts/ftMonitor_GHDLSim.sh'],stdout=subprocess.PIPE)
				subprocess.run(['mv',__VHDLDIR__+'ftMuMonitor/sim/result/async_out.txt',filename],stdout=subprocess.PIPE)
		f.close()
	for tmp in ('tmp.ftasm','tmp.ftm','tmp.fti','tmp.ftscq'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)
	
'''

'''
def test_board():
	pass

'''
The main method for this file.
	- Parses the directories for the input traces and the formula files.
	- Parses the input arguement, to determine if you are running a test or cleaning the directories.
	- If running the test,determines which version of R2U2 you want to test.
'''
def main():
	args = parserInfo()
    # If there is the remove flag, remove all directories and files in the results directory
	if(args['remove']):
		print('Removing all R2U2 log files from the results directory')
		shutil.rmtree(__ResultDIR__+__ResultCDir__, ignore_errors=True)
		shutil.rmtree(__ResultDIR__+__ResultCppDir__, ignore_errors=True)
		shutil.rmtree(__ResultDIR__+__ResultVHDLDir__, ignore_errors=True)

	# If not, then test the specified version of R2U2
	elif(args['version']):
		formulaFiles,inputFiles = list_file()
		elif(args['version'].lower()=='c'):
			test_c(formulaFiles,inputFiles)
		elif(args['version'].lower()=='cpp'):
			test_cpp(formulaFiles,inputFiles)
		elif(args['version'].lower()=='vhdl'):
			test_vhdl(formulaFiles,inputFiles)
		else:
			print('unknown argument')
	# Else, throw an error message
	else:
		print('ERROR: Invalid arguement flags or missing input arguement after flag')
		print('Use "-h" flag for more information')

if __name__ == "__main__":
   main()
