from .Observer import *
__all__ = ['cnt2observer', 'parser']

operator_cnt = 0
cnt2observer={}

def queue_size_assign(predLen = 0):
	visited = set()
	predLen = predLen
	def get_node_set(node):
		if(node!=None):
			if(node.type=='ATOMIC'):
				node.bcd = -1*predLen				
				node.set_scq_size(2) # interesting part of the real implementation
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
			size1 = max(left.scq_size,right.wcd-left.bcd+1)
			size2 = max(right.scq_size,left.wcd-right.bcd+1)
			left.set_scq_size(size1) # init the SCQ in observer with specified size
			right.set_scq_size(size2)  # init the SCQ in observer with specified size
		else:
			left = n.input_1
			queue_size_assign_helper(left)
			if(n.type == 'NEG' or n.type == 'END'):
				n.bcd, n.wcd = left.bcd, left.wcd
			else:
				n.bcd, n.wcd = left.bcd + n.lb, left.wcd + n.ub
		n.set_scq_size(n.scq_size+1) # increase by 1 to prevent null pointer
		visited.add(n)

	def get_total_size(node):
		if(node and node not in visited):
			visited.add(node)
			print(node.name,'	',node,':	',node.scq_size)
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

	top = cnt2observer[len(cnt2observer)-1]
	get_node_set(top)
	top.set_scq_size(1) # prevent null pointer to SCQ, needs attention
	queue_size_assign_helper(top)

	visited = set()#clear the set for other purpose
	totsize = get_total_size(top)
	visited = set()#clear the set for other purpose
	return totsize,get_total_pred_time(top)


def decode_assembly(assembly):
	# construct the SCQ connection first
	str2observer = {}
	global cnt2observer
	cnt = 0
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
			str2observer[target] = GLOBAL(str2observer[token[2]],int(token[3]),int(token[4]))
		elif(op=='and'):
			str2observer[target] = AND(str2observer[token[2]],str2observer[token[3]])
		elif(op=='until'):
			print(token)
			str2observer[target] = UNTIL(str2observer[token[2]],str2observer[token[3]],int(token[4]),int(token[5]))
		elif(op=='end'):
			str2observer[target] = END(str2observer[token[2]])
		else:
			print('Invalid operator, exit')
			quit()
		cnt2observer[cnt]=str2observer[target]
		cnt+=1
	return cnt2observer
