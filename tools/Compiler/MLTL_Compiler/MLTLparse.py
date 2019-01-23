# ------------------------------------------------------------
# TLparse.py
#
# Parser for MTL formula.
# Construct observer abstract syntax tree
# Syntax : https://ti.arc.nasa.gov/m/profile/kyrozier/PANDA/PANDA.html
# ------------------------------------------------------------
import ply.yacc as yacc
from .MLTLlex import tokens
from .Observer import *
import sys

__all__ = ['cnt2observer', 'parser']

operator_cnt = 0
cnt2observer = {}

def record_operators(ob):
	global operator_cnt	
	cnt2observer[operator_cnt] = ob
	operator_cnt += 1

def p_MLTL_operators(p):
	'''
	expression 	: expression AND expression
				| NEG expression
				| NEXT expression
				| expression OR expression
				| GLOBAL LBRACK NUMBER RBRACK expression
				| GLOBAL LBRACK NUMBER COMMA NUMBER RBRACK expression
				| expression UNTIL LBRACK NUMBER RBRACK expression
				| expression UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression				
	'''
	if p[1] == '-':
		p[0] = NEG(p[2])
	elif p[1] == 'X':
		p[0] = GLOBAL(p[2],lb=1,ub=1)
	elif len(p)>2 and p[2] == '&':
	 	p[0] = AND(p[1],p[3])
	elif len(p)>2 and p[2] == '|':
	 	p[0] = NEG(AND(NEG(p[1]),NEG(p[3])))
	 	# p[0] = OR(p[1],p[3])
	elif p[1] == 'G' and len(p) == 6:
		p[0] = GLOBAL(p[5],ub=p[3])
	elif p[1] == 'G' and len(p)==8:
		p[0] = GLOBAL(p[7],lb=p[3],ub=p[5])
	elif p[2] == 'U' and len(p)==7:
		p[0] = UNTIL(p[1],p[6],ub=p[4])
	elif p[2] == 'U' and len(p)==9:
		p[0] = UNTIL(p[1],p[8],lb=p[4],ub=p[6])
	else:
		raise Exception('Syntax error in type! Cannot find matching format.')
		sys.exit(0)
	record_operators(p[0])

def p_paren_token(p):
	'''expression : LPAREN expression RPAREN'''
	p[0] = p[2]

def p_atomic_token(p):
	'''expression : ATOMIC'''
	p[0] = ATOM(p[1])
	record_operators(p[0])

precedence = (
	('left', 'AND'),
	('left', 'GLOBAL', 'UNTIL'),	
	('left', 'NEG'),
	('left', 'LPAREN', 'RPAREN','ATOMIC','LBRACK','RBRACK'),
)

# Error rule for syntax errors
def p_error(p):
	print("Syntax error in input!")

# Build the parser
parser = yacc.yacc()

###############################################################
# Optimize the AST
def optimize():
	# Map inorder traverse to observer node, use '(' and ')' to represent boundry
	def inorder(root,m):
		if(root==None):
			return []
		link = ['(']
		link.extend(inorder(root.left,m))
		if(root.tag==0):
			link.extend([root.name])
		else:
			link.extend([root.tag])
		link.extend(inorder(root.right,m))
		link.append(')')
		tup = tuple(link)
		if(tup in m):
			# find left of right branch of pre node
			if(root.pre.left==root):
				root.pre.left = m[tup]
			else:
				root.pre.right = m[tup]
		else:
			m[tup] = root
		return link

	# inorder traverse from the top node
	top = cnt2observer[len(cnt2observer)-1]
	inorder(top,{})

###############################################################
# Sort the processing node sequence, the sequence is stored in stack
def sort_node():
	top = cnt2observer[len(cnt2observer)-1]
	# collect used node from the tree
	def checkTree(root, graph):
		if(root==None):
			return
		checkTree(root.left, graph);
		graph.add(root)
		checkTree(root.right, graph);

	graph=set()
	checkTree(top,graph)

	def topologicalSortUtil(root, visited, stack):
		if(root!=None and not visited[root]):
			visited[root] = True
			[topologicalSortUtil(i,visited,stack) for i in(root.left, root.right)]
			stack.insert(0,root)

	def topologicalSort(root, graph):
		visited = {}
		for node in graph:
			visited[node]=False 
		stack = []
		[topologicalSortUtil(node,visited,stack) for node in graph]
		stack.reverse()
		return stack

	stack = topologicalSort(top,graph)
	return stack

# Generate assembly code
def gen_assembly():	
	stack = sort_node()
	s=""
	for node in stack:
		s = node.gen_assembly(s)
	s = s+'s'+str(len(stack))+': end s'+str(len(stack)-1) # append the end command
	print(s)





