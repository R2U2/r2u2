from .Observer import *
# __all__ = ['cnt2observer', 'parser']

# operator_cnt = 0
# cnt2observer={}


class Assembly():
	def __init__(self,MLTL_ASSEMBLY):
		self.valid_node_set = []
		decode_assembly(self,MLTL_ASSEMBLY)
		self.queue_size_assign() # assign SCQ size

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
					if(n.type == 'NEG' or n.type == 'END'):
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

		compute_propagation_delay()
		compute_scq_size()		
		return get_total_size()

def decode_assembly(self,assembly):
	# construct the SCQ connection first
	str2observer = {}
	f = assembly
	for line in f.splitlines():
		token = line.split()
		target,op = token[0][:-1],token[1] # remove the symbol ':' for target
		if(op=='load'):
			str2observer[target] = ATOM(token[2])
		elif(op=='not'):
			str2observer[target] = NEG(str2observer[token[2]])
		elif(op=='boxbox'):
			str2observer[target] = GLOBAL(str2observer[token[2]],int(token[3]))
		elif(op=='boxdot'):
			str2observer[target] = GLOBAL(str2observer[token[2]],int(token[4]),int(token[3]))
		elif(op=='and'):
			str2observer[target] = AND(str2observer[token[2]],str2observer[token[3]])
		elif(op=='until'):
			str2observer[target] = UNTIL(str2observer[token[2]],str2observer[token[3]],int(token[5]),int(token[4]))
		elif(op=='end'):
			str2observer[target] = END(str2observer[token[2]])
		elif(op=='TRUE'):
			str2observer[target] = BOOL('TRUE')
		elif(op=='FALSE'):
			str2observer[target] = BOOL('FALSE')
		else:
			print(op)
			print('Invalid operator, exit')
			quit()
		self.valid_node_set.append(str2observer[target])
