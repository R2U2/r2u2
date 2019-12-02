from ACOW import *
import argparse

# User defined automaton

# def define_automaton():
# 	a = automaton()
# 	#sg = StateGen(3,'s','a')
# 	a.INITIAL_STATE = 's2'
# 	a.DEST_STATE = 's3'
# 	#a.STATE, a.DELTA = sg.gen_aut()
# 	a.STATE = {
# 	's0':{'a0':0,'a1':0},
# 	's1':{'a0':0,'a1':1},
# 	's2':{'a0':1,'a1':0},
# 	's3':{'a0':1,'a1':1},
# 	}
# 	a.DELTA = {
# 	's0': {'s0','s1','s2','s3'},
# 	's1': {'s0','s1','s2','s3'},
# 	's2': {'s0','s1','s2','s3'},
# 	's3': {'s0','s1','s2','s3'},
# 	}
# 	print(a)
# 	return a


def formula_input(MLTL,optimize_cse=True):
	newAST = Postgraph(MLTL,optimize_cse=optimize_cse)
	return newAST.valid_node_set

def assembly_input(MLTL):
	newAST = Assembly(MLTL)
	return newAST.valid_node_set 

def parserInfo():
	parser = argparse.ArgumentParser(description='ACOW: Model Checking tool for MLTL')
	parser.add_argument('-m','--mltl', help='Choose MLTL formula', required=True)
	parser.add_argument('-o','--output', help='Output file name', required=False)
	group = parser.add_mutually_exclusive_group(required=True)
	group.add_argument('-a','--atomic',help='Give the input as atomic')
	group.add_argument('-s','--sensor',help='Give the input in raw sensor signal')
	args = vars(parser.parse_args())
	return args


def main():
	# a = define_automaton()
	# a.init()
	args = parserInfo()
	MLTL = args['mltl']
	output_file_name = args['output'] if args['output'] else 'untitled.txt'
	if(':' in MLTL): # the input is the assembly file name
		valid_node_set = assembly_input(MLTL)
	else: # the input is one line MLTL string
		valid_node_set = formula_input(MLTL)
	if(args['atomic']):
		solution = Traverse(valid_node_set,args['atomic'],isAtomic=True,output_file_name=output_file_name)
	else:
		solution = Traverse(valid_node_set,args['sensor'],isAtomic=False,output_file_name=output_file_name)
	print(solution.run())
	# solution = Search(a,valid_node_set,agent='DES')

if __name__ == "__main__":
	main()
