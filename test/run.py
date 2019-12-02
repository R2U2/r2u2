import os
import argparse
import subprocess
import re
from subprocess import check_output

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__TLDir__ = __AbsolutePath__+'TL_formula/'
__InputDir__ = __AbsolutePath__+'Inputs/'
__PythonDir__ = __AbsolutePath__+'../R2U2_SW/R2U2_PYTHON/'
__CDir__ = __AbsolutePath__+'../R2U2_SW/R2U2_C/'
__CPPDIR__ = __AbsolutePath__+'../R2U2_SW/R2U2_CPP/'
__VHDLDIR__ = __AbsolutePath__+'../R2U2_HW/'
__ResultDIR__ = __AbsolutePath__+'results/'
__CompilerDir__ = __AbsolutePath__+'../tools/Compiler/'
__BinGenDir__ = __AbsolutePath__+'../tools/AssemblyToBinary/'

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

def post_python_version_process(file):
	# Reformat the output file
	f=open(file,'r')
	f_temp = open(file+'_tmp','w')
	# lines =  [i.strip() for i in f]
	redundent_pc = r'PC:[\d](\s*)(?=(PC:[\d]+|\n))'
	atomic_value  = r'(?<=LOAD\s)[a-zA-Z0-9]+\s'
	content = re.sub(atomic_value,"",re.sub(redundent_pc,"",f.read()))
	f_temp.write(content)
	f.close()
	f_temp.close()
	os.rename(file+'_tmp', file)



def subprocess_cmd(command):
	process = subprocess.Popen(command,stdout=subprocess.PIPE, shell=True)
	proc_stdout = process.communicate()[0].strip()
	print(proc_stdout)

def preprocessVHDLinput(input_case):
	f = open(input_case)
	lines =  [i.strip() for i in f][1:] # remove first line (first line is the atomic name, useless in VHDL test)
	output_case = []
	fw= open(__VHDLDIR__+"ftMuMonitor/sim/testcases/atomic.trc","w+") # location of the trace file for tb.vhd
	for each_atomic in lines:
		fw.write(each_atomic.replace(" ","").replace(",","")+'\n')
	fw.close()
	f.close()


def gen_assembly(MLTL,timestamp_byte = 4,gen_bin = False):
	subprocess.run(["python", __CompilerDir__+'main.py',MLTL], stdout=subprocess.PIPE)
	f = open('tmp.ftasm')
	asm = f.read()
	f.close()
	if gen_bin:
		subprocess.run(["python", __BinGenDir__+'ftas.py','tmp.ftasm',str(timestamp_byte)], stdout=subprocess.PIPE)
	return asm


# python ../R2U2_SW/R2U2_PYTHON/MLTL_main.py -m G[3]a0 -a Inputs/case_1
#  python ../R2U2_SW/R2U2_PYTHON/MLTL_main.py -m "$(cat tmp.ftasm)" -a Inputs/case_0
def test_python(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+'python_version/'
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	for _formulaFile in formulaFiles:
		f = open(__TLDir__+_formulaFile,'r')
		lines =  [i.strip() for i in f]
		for cnt,formula in enumerate(lines):
			asm = gen_assembly(formula)
			for _input in inputFiles:
				filename = __OutputDIR__+     _formulaFile+_input+'formula_'+str(cnt)+'.txt'
				# filename = __OutputDIR__+_formulaFile+'_case'+str(cnt)+'.txt'
				print(filename)
				subprocess.run(["python", __PythonDir__+'MLTL_main.py','-m',asm,'-a',__InputDir__+_input,'-o',filename],stdout=subprocess.PIPE)
				post_python_version_process(filename)
		f.close()
	for tmp in ('tmp.ftasm','tmp.ftscq'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)


# ../R2U2_SW/R2U2_C/bin/r2u2 Inputs/case_0 tmp.ftm tmp.fti tmp.ftscq
def test_c(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+'c_version/'
	# subprocess_cmd('cd '+__CDir__+'; '+'make') # compile C version
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	for _formulaFile in formulaFiles:
		f = open(__TLDir__+_formulaFile,'r')
		lines =  [i.strip() for i in f]
		for cnt,formula in enumerate(lines):
			gen_assembly(formula,4,True)
			for _input in inputFiles:
				filename = __OutputDIR__+_formulaFile+_input+'formula_'+str(cnt)+'.txt'
				print(filename)
				# subprocess.run([__CDir__+'bin/r2u2',__InputDir__+_input,'tmp.ftm','tmp.fti','tmp.ftscq'],stdout=subprocess.PIPE)
				subprocess.run([__CDir__+'bin/r2u2',__InputDir__+_input,'tmp.ftm','tmp.fti','tmp.ftscq'])
				subprocess.run(['mv','R2U2.log',filename],stdout=subprocess.PIPE)
		f.close()
	for tmp in ('tmp.ftasm','tmp.ftm','tmp.fti','tmp.ftscq','R2U2.out'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)


# def test_c():
# 	pass

def test_cpp(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+'cpp_version/'
	# subprocess_cmd('cd '+__CPPDIR__+'; '+'make') # compile Cpp version
	if not os.path.exists(__OutputDIR__):
		os.makedirs(__OutputDIR__)
	for _formulaFile in formulaFiles:
		f = open(__TLDir__+_formulaFile,'r')
		lines =  [i.strip() for i in f]
		for cnt,formula in enumerate(lines):
			gen_assembly(formula,4,True)
			for _input in inputFiles:
				filename = __OutputDIR__+_formulaFile+_input+'formula_'+str(cnt)+'.txt'
				print(filename)
				subprocess.run([__CPPDIR__+'build/app/MLTL','tmp.ftasm',__InputDir__+_input,"result.txt"])
				print(__CPPDIR__+'build/app/MLTL')
				# quit()
				subprocess.run(['mv','result.txt',filename],stdout=subprocess.PIPE)
		f.close()
	for tmp in ('tmp.ftasm','tmp.ftm','tmp.fti','tmp.ftscq','result.txt'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)

	

def test_vhdl(formulaFiles,inputFiles):
	__OutputDIR__ = __ResultDIR__+'vhdl_version/'
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
				filename = __OutputDIR__+     _formulaFile+_input+'formula_'+str(cnt)+'.txt'
				print(filename)
				
				subprocess.run(['bash',__VHDLDIR__+'GHDL_scripts/ftMonitor_GHDLSim.sh'],stdout=subprocess.PIPE)
				subprocess.run(['mv',__VHDLDIR__+'ftMuMonitor/sim/result/async_out.txt',filename],stdout=subprocess.PIPE)
		f.close()
	for tmp in ('tmp.ftasm','tmp.ftm','tmp.fti','tmp.ftscq'):
		subprocess.run(['rm',tmp], stdout=subprocess.PIPE)
	

def test_board():
	pass

def main():
	args = parserInfo()
	formulaFiles,inputFiles = list_file()
	if(args['version'].lower()=='python'):
		test_python(formulaFiles,inputFiles)
	elif(args['version'].lower()=='c'):
		test_c(formulaFiles,inputFiles)
	elif(args['version'].lower()=='cpp'):
		test_cpp(formulaFiles,inputFiles)
	elif(args['version'].lower()=='vhdl'):
		test_vhdl(formulaFiles,inputFiles)
	else:
		print('unknown argument')

if __name__ == "__main__":
   main()