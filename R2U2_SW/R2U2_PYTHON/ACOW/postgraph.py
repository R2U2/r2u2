## Description: 1. optimize the AST; 2. assign SCQ size; 3. generate assembly
## Author: Pei Zhang
from .MLTLparse import *
from .Observer import *

class Postgraph():
	def __init__(self,MLTL,optimize_cse=True):
		parser.parse(MLTL)
		self.top = cnt2observer[len(cnt2observer)-1]
		if(optimize_cse):
			self.optimize_cse()
		self.valid_node_set = self.sort_node() # topological reorder the node, from child to parent
		print(cnt2observer)
		self.queue_size_assign() # assign SCQ size
		self.gen_assembly() # generate assembly, can be commented

	###############################################################
	# Common subexpression elimination the AST
	def optimize_cse(self):
		# Map inorder traverse to observer node, use '(' and ')' to represent boundry
		if(len(cnt2observer)==0):
			return
		def inorder(root,m):
			if(root==None):
				return []
			link = ['(']
			link.extend(inorder(root.left,m))
			link.extend([root.name])
			link.extend(inorder(root.right,m))
			link.append(')')
			tup = tuple(link)
			if(tup in m):
				# find left of right branch of pre node
				if(root.parent.left==root):
					root.parent.left = m[tup]
				else:
					root.parent.right = m[tup]
			else:
				m[tup] = root
			return link

		# inorder traverse from the top node
		inorder(self.top,{})

	# TODO: logically optimize the AST, e.g., a0&a0->a0; a0&!a0=FALSE
	def optimize_logic(self):
		pass

	###############################################################
	# Topological sort the node sequence, the sequence is stored in stack
	def sort_node(self):
		if(len(cnt2observer)==0):
			return []
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
			if(root!=None and root not in visited):
				visited.add(root)
				[topologicalSortUtil(i,visited,stack) for i in(root.left, root.right)]
				stack.insert(0,root)

		def topologicalSort(root, graph):
			visited = set()
			stack = []
			[topologicalSortUtil(node,visited,stack) for node in graph]
			return stack 

		stack = topologicalSort(top,graph)
		stack.reverse()
		return stack # child to parent

	###############################################################
	# Assign the size for each queue
	def queue_size_assign(self,predLen = 0):
		stack = self.valid_node_set # child to parent

		# compute propagation delay from bottom up
		def compute_propagation_delay():
			for n in stack:
				if(n.type=='ATOMIC'):
					n.bpd = -1*predLen
					n.scq_size = 1
				elif(n.type=='BOOL'):
					n.bpd = 0
					n.scq_size = 1
				elif(n.type=='AND' or n.type=='OR' or n.type=='UNTIL' or n.type=='WEAK_UNTIL'):
					left, right = n.left, n.right
					if(n.type=='AND' or n.type=='OR'):
						n.bpd, n.wpd = min(left.bpd, right.bpd), max(left.wpd, right.wpd)
					else:
						n.bpd, n.wpd = min(left.bpd, right.bpd)+n.lb, max(left.wpd, right.wpd)+n.ub
				else:	
					left = n.left
					if(n.type == 'NEG'): # no need to consider 'END' observer
						n.bpd, n.wpd = left.bpd, left.wpd
					else:
						print(n.type)
						n.bpd, n.wpd = left.bpd + n.lb, left.wpd + n.ub
				n.scq_size += 1 # (June.25,2019) Intentionally plue 1 here. Python version use different mentod to check SCQ emptyness

		# compute scq size from top down
		def compute_scq_size():
			for n in stack:
				if(n.left and n.right):
					left, right = n.left, n.right;			
					left.scq_size = max(right.wpd-left.bpd+1, left.scq_size)
					right.scq_size = max(left.wpd-right.bpd+1, right.scq_size)

		def get_total_size():
			totsize = 0
			print("(Intentionally increase all SCQ size by 1. Python version use a different method to check SCQ emptyness.)")
			for n in stack:
				n.set_scq_size()
				print(n.name,'	',n,' SCQ size',':	(',n.scq_size,')')
				totsize += n.scq_size
			return totsize

		def generate_scq_size_file():
			s=""
			pos = 0
			for n in stack:
				st_pos = pos
				ed_pos = st_pos+n.scq_size
				pos = ed_pos+1;
				s = s+'{0:08b}'.format(st_pos)+'{0:08b}'.format(ed_pos)+'\n'
			with open("tmp.ftscq","w+") as f:
				f.write(s)

		compute_propagation_delay()
		compute_scq_size()
		# generate_scq_size_file() # run this function if you want to generate c SCQ configuration file
		return get_total_size()

	# Generate assembly code
	def gen_assembly(self):	
		stack = self.valid_node_set
		s=""
		if(len(stack)==0):
			return s
		for node in stack:
			s = node.gen_assembly(s)
		s = s+'s'+str(len(stack))+': end s'+str(len(stack)-1) # append the end command
		print(s)
		with open("tmp.ftasm","w+") as f:
			f.write(s)

