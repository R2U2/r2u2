# ------------------------------------------------------------
# MTLparse.py
#
# Parser for MTL formula.
# Construct observer abstract syntax tree and remove the duplicate branch
# ------------------------------------------------------------
import ply.yacc as yacc
from .MTLlex import tokens
from .Observer import *
import sys

__all__ = ['cnt2observer', 'parser','Syntax_Correct']

operator_cnt = 0
cnt2observer={}
Syntax_Correct = True



def record_operators(ob):
	global operator_cnt
	global Syntax_Correct
	cnt2observer[operator_cnt] = ob
	operator_cnt += 1
	Syntax_Correct = False

def reset():
	pass
	# global parser
	# global Syntax_Correct
	# global tagMap
	# global cnt2observer
	# operator_cnt = 0
	
	# cnt2observer={}
	# parser = yacc.yacc()
	#Syntax_Correct = True


def p_MTL_operators(p):
	'''
	expression 	: expression AND expression
				| expression OR expression
				| NEG expression
				| GLOBAL LBRACK NUMBER RBRACK expression
				| GLOBAL LBRACK NUMBER COMMA NUMBER RBRACK expression
				| FUTURE LBRACK NUMBER RBRACK expression
				| FUTURE LBRACK NUMBER COMMA NUMBER RBRACK expression
				| expression UNTIL LBRACK NUMBER RBRACK expression
				| expression UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression
				| expression WEAK_UNTIL LBRACK NUMBER RBRACK expression
				| expression WEAK_UNTIL LBRACK NUMBER COMMA NUMBER RBRACK expression			
	'''
	if p[1] == '!':
		p[0] = NEG(p[2])
	elif len(p)>2 and p[2] == '&':
	 	p[0] = AND(p[1],p[3])
	elif len(p)>2 and p[2] == '|':
	 	p[0] = OR(p[1],p[3])
	elif p[1] == 'G' and len(p) == 6:
		p[0] = GLOBAL(p[5],ub=p[3])
	elif p[1] == 'G' and len(p)==8:
		p[0] = GLOBAL(p[7],lb=p[3],ub=p[5])
	elif p[1] == 'F' and len(p) == 6:
		p[0] = FUTURE(p[5],ub=p[3])
	elif p[1] == 'F' and len(p)==8:
		p[0] = FUTURE(p[7],lb=p[3],ub=p[5])
	elif p[2] == 'U' and len(p)==7:
		p[0] = UNTIL(p[1],p[6],ub=p[4])
	elif p[2] == 'U' and len(p)==9:
		p[0] = UNTIL(p[1],p[8],lb=p[4],ub=p[6])
	elif p[2] == 'W' and len(p)==7:
		p[0] = WEAK_UNTIL(p[1],p[6],ub=p[4])
	elif p[2] == 'W' and len(p)==9:
		p[0] = WEAK_UNTIL(p[1],p[8],lb=p[4],ub=p[6])
	else:
		global Syntax_Correct
		Syntax_Correct = False
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
	('left', 'AND', 'OR'),
	('left', 'GLOBAL', 'FUTURE', 'UNTIL','WEAK_UNTIL'),	
	('left', 'NEG'),
	('left', 'LPAREN', 'RPAREN','ATOMIC','LBRACK','RBRACK'),
)

# Error rule for syntax errors
def p_error(p):
	global Syntax_Correct
	Syntax_Correct = False
	print("Syntax error in input!")

# Build the parser
parser = yacc.yacc()

# Optimize the AST (Build AST first and then optimize. Finally map the observer to AST)
def optimize():
	# Map inorder traverse to observer node, use '(' and ')' to represent boundry
	def inorder(root,m):
		if(root==None):
			return []
		link = ['(']
		link.extend(inorder(root.input_1,m))
		link.extend([root.name])
		link.extend(inorder(root.input_2,m))
		link.append(')')
		tup = tuple(link)
		if(tup in m):
			# find left or right branch of pre node
			if(root.parent.input_1==root):
				root.parent.input_1 = m[tup]
			else:
				root.parent.input_2 = m[tup]
		else:
			m[tup] = root
		return link

	# inorder traverse from the top node
	top = cnt2observer[len(cnt2observer)-1]
	inorder(top,{})
	return sort_node()




###############################################################
# Sort the processing node sequence, the sequence is stored in stack
def sort_node():
	top = cnt2observer[len(cnt2observer)-1]
	# collect used node from the tree
	def checkTree(root, graph):
		if(root==None):
			return
		checkTree(root.input_1, graph);
		graph.add(root)
		checkTree(root.input_2, graph);

	graph=set()
	checkTree(top,graph)

	def topologicalSortUtil(root, visited, stack):
		if(root!=None and not visited[root]):
			visited[root] = True
			[topologicalSortUtil(i,visited,stack) for i in(root.input_1, root.input_2)]
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


def queue_size_assign(predLen = 0):
	visited = set()
	predLen = predLen
	def get_node_set(node):
		if(node!=None):
			if(node.type=='ATOMIC'):
				node.bcd = -1*predLen
				visited.add(node)
			else:
				get_node_set(node.input_1)
				get_node_set(node.input_2)


	def queue_size_assign_helper(n):
		if(n in visited):
			return
		if(n.type=='AND' or n.type=='OR' or n.type=='UNTIL' or n.type=='WEAK_UNTIL'):
			left, right = n.input_1, n.input_2
			queue_size_assign_helper(left)
			queue_size_assign_helper(right)
			if(n.type=='AND' or n.type=='OR'):
				n.bcd, n.wcd = min(left.bcd, right.bcd), max(left.wcd, right.wcd)
			else:
				n.bcd, n.wcd = min(left.bcd, right.bcd)+n.lb, max(left.wcd, right.wcd)+n.ub
			left.scq_size = max(left.scq_size,right.wcd-left.bcd+1)
			right.scq_size = max(right.scq_size,left.wcd-right.bcd+1)
			left.set_scq_size(left.scq_size) # init the SCQ in observer with specified size
			right.set_scq_size(right.scq_size)  # init the SCQ in observer with specified size
		else:
			left = n.input_1
			queue_size_assign_helper(left)
			if(n.type == 'NEG'):
				n.bcd, n.wcd = left.bcd, left.wcd
			else:
				n.bcd, n.wcd = left.bcd + n.lb, left.wcd + n.ub

		visited.add(n)

	def get_total_size(node):
		if(node and node not in visited):
			visited.add(node)
			#print(node.name,'	',node,':	',node.scq_size)
			return get_total_size(node.input_1)+get_total_size(node.input_2)+node.scq_size
		return 0

	def get_total_pred_time(node):
		if(node and node not in visited):
			visited.add(node)
			if(node.input_1==None):#atomic
				return predLen+1
			if(node.input_2==None):#Unary Operator
				return get_total_pred_time(node.input_1)+ predLen+1
			#print(node.name,'	',node,':	',node.scq_size)
			return get_total_pred_time(node.input_1)+get_total_pred_time(node.input_2)+node.input_1.scq_size+node.input_2.scq_size
		return 0


	top = cnt2observer[len(cnt2observer)-1]
	get_node_set(top)
	queue_size_assign_helper(top)

	visited = set()#clear the set for other purpose
	totsize = get_total_size(top)
	visited = set()#clear the set for other purpose
	return totsize,get_total_pred_time(top)


# Generate assembly code
def gen_assembly():	
	stack = sort_node()
	s=""
	for node in stack:
		s = node.gen_assembly(s)
	s = s+'s'+str(len(stack))+': end s'+str(len(stack)-1) # append the end command
	print(s)
	return s


# serialize the architecture for GUI plot
# use recursive layer by layer traverse
def gen_serialization():
	def gen_serialization_helper(nodeList):		
		if(len(nodeList)==0):
			return ""
		s = ""
		newList = []
		for n in nodeList:
			if(n==None):
				s+=('None'+'#')
				continue
			if(n in exist):
				s+='*'+n.name+'['+str(n.scq_size)+','+'('+str(n.bcd)+'~'+str(n.wcd)+')'+']'+'tag:'+str(tagMap[n])+'#'
				newList.extend([None,None])
				continue
			s+=n.name+'['+str(n.scq_size)+','+'('+str(n.bcd)+'~'+str(n.wcd)+')'+']'+'tag:'+str(tagMap[n])+'#'
			exist.add(n)
			for subNode in [n.input_1,n.input_2]:	
				newList.append(subNode)

		s+=gen_serialization_helper(newList)
		return s
	exist = set() # use map to record that a node has appeared
	top = cnt2observer[len(cnt2observer)-1]

	tagMap = {}
	for key,val in cnt2observer.items():
		tagMap[val] = key

	res = gen_serialization_helper([top,])
	if(len(res)>0 and res[-1]=='#'):
		res = res[:-1]
	return res
	
