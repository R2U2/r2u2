from ACOW import *
import argparse

# User defined automaton
'''
def define_automaton():
	a = automaton()
	#sg = StateGen(3,'s','a')
	a.INITIAL_STATE = 's2'
	a.DEST_STATE = 's3'
	#a.STATE, a.DELTA = sg.gen_aut()
	a.STATE = {
	's0':{'a0':0,'a1':0},
	's1':{'a0':0,'a1':1},
	's2':{'a0':1,'a1':0},
	's3':{'a0':1,'a1':1},
	}
	a.DELTA = {
	's0': {'s0','s1','s2','s3'},
	's1': {'s0','s1','s2','s3'},
	's2': {'s0','s1','s2','s3'},
	's3': {'s0','s1','s2','s3'},
	}
	print(a)
	return a
'''

def bare_input(MLTL,optimize=True):
	from ACOW import MLTLparse
	top_node = MLTLparse.parser.parse(MLTL)
	if optimize:
		cnt2observer = MLTLparse.optimize() # comment this line if you don't want to optimze the AST
	SCQ_size, _ = MLTLparse.queue_size_assign()
	MLTLparse.gen_assembly()
	return cnt2observer

def assembly_input(MLTL):
	from ACOW import Assembly
	cnt2observer = Assembly.decode_assembly(MLTL)
	SCQ_size, _ = Assembly.queue_size_assign()
	return cnt2observer

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
	#a.show()# show a .pdf figure of the state space model
	args = parserInfo()
	MLTL = args['mltl']
	output_file_name = args['output'] if args['output'] else 'untitled.txt'
	if(':' in MLTL): # the input is the assembly file name
		cnt2observer = assembly_input(MLTL)
	else: # the input is one line MLTL string
		cnt2observer = bare_input(MLTL)
	if(args['atomic']):
		solution = Traverse(cnt2observer,args['atomic'],isAtomic=True,output_file_name=output_file_name)
	else:
		solution = Traverse(cnt2observer,args['sensor'],isAtomic=False,output_file_name=output_file_name)

	print(solution.run())
	#solution = Search(a,cnt2observer,agent='DES')
	#solution.run(['s0','s0','s0','s1','s1','s1','s1','s1','s1','s1','s3','s2','s2','s3','s2','s3','s3','s3','s3','s2','s2','s3','s3','s3','s3','s0','s1','s1','s1','s0','s0'])

if __name__ == "__main__":
	main()
