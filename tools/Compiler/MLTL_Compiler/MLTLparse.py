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
	if p[1] == '!':
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

def p_bool_token(p):
	'''
	expression : TRUE
				| FALSE
	'''
	if p[1] == 'TRUE':
		p[0] = BOOL('TRUE')
	elif p[1] == 'FALSE':
		p[0] = BOOL('FALSE')

precedence = (
	('left', 'AND', 'OR'),
	('left', 'GLOBAL', 'UNTIL'),	
	('left', 'NEG','NEXT'),
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
	if(len(cnt2observer)==0):
		return
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
	if(len(cnt2observer)==0):
		return []
	top = cnt2observer[len(cnt2observer)-1]
	# collect used node from the tree
	def checkTree(root, graph):
		if(root==None or root.type=='BOOL'):
			return
		checkTree(root.left, graph);
		graph.add(root)
		checkTree(root.right, graph);

	graph=set()
	checkTree(top,graph)

	def topologicalSortUtil(root, visited, stack):
		if(root!=None and root.type!='BOOL' and not visited[root]):
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

###############################################################
# Assign the size for each queue
def queue_size_assign(predLen = 0):
	visited = set()
	predLen = predLen
	def get_node_set(node):
		if(node!=None):
			if(node.type=='ATOMIC'):
				node.bpd = -1*predLen				
				node.set_scq_size(1) # interesting part of the real implementation
				visited.add(node)
			elif (node.type=='BOOL'):
				node.bpd = 0
				node.set_scq_size(0) # interesting part of the real implementation
				visited.add(node)
			else:
				get_node_set(node.left)
				get_node_set(node.right)


	def queue_size_assign_helper(n):
		if(n in visited):
			return
		if(n.type=='AND' or n.type=='OR' or n.type=='UNTIL' or n.type=='WEAK_UNTIL'):
			left, right = n.left, n.right
			queue_size_assign_helper(left)
			queue_size_assign_helper(right)
			if(n.type=='AND' or n.type=='OR'):
				n.bpd, n.wpd = min(left.bpd, right.bpd), max(left.wpd, right.wpd)
			else:
				n.bpd, n.wpd = min(left.bpd, right.bpd)+n.lb, max(left.wpd, right.wpd)+n.ub
			size1 = max(left.scq_size,right.wpd-left.bpd+1)
			size2 = max(right.scq_size,left.wpd-right.bpd+1)
			left.set_scq_size(size1) # init the SCQ in observer with specified size
			right.set_scq_size(size2)  # init the SCQ in observer with specified size
		else:
			left = n.left
			queue_size_assign_helper(left)
			if(n.type == 'NEG'):
				n.bpd, n.wpd = left.bpd, left.wpd
			else:
				n.bpd, n.wpd = left.bpd + n.lb, left.wpd + n.ub
		n.set_scq_size(n.scq_size) # increase by 1 to prevent null pointer -- removed +1 on Feb.20.2019
		visited.add(n)

	def get_total_size(node):
		if(node and node not in visited):
			visited.add(node)
			print(node.name,'	',node,':	',node.scq_size)
			return get_total_size(node.left)+get_total_size(node.right)+node.scq_size
		return 0

	top = cnt2observer[len(cnt2observer)-1]
	get_node_set(top)
	top.set_scq_size(1) # prevent null pointer to SCQ, needs attention
	queue_size_assign_helper(top)

	visited = set()#clear the set for other purpose
	totsize = get_total_size(top)
	return totsize

# Generate assembly code
def gen_assembly():	
	stack = sort_node()
	s=""
	if(len(stack)==0):
		return s
	for node in stack:
		s = node.gen_assembly(s)
	s = s+'s'+str(len(stack))+': end s'+str(len(stack)-1) # append the end command
	print(s)





