## Description: Double linked observer syntex tree
## Author: Pei Zhang

class Observer():
	line_cnt = 0 #static var to record line number
	def __init__(self, left=None, right=None):
		self.left = left
		self.right = right
		self.pre = None
		self.hook = -1
	
	def gen_assembly(self, s, substr):
		self.hook = 's'+str(Observer.line_cnt)
		s += self.hook+": "+substr+'\n'
		Observer.line_cnt += 1
		return s

class ATOM(Observer):
	def __init__(self, name):
		super().__init__()
		self.label = 'ATOM'
		self.tag = 0
		self.name = name

	def gen_assembly(self, s):
		substr = "load "+self.name
		s = super().gen_assembly(s, substr)
		return s
		


class NEG(Observer):
	def __init__(self, left):
		super().__init__(left)
		self.label = 'NEG'
		self.tag = 1
		self.left.pre = self

	def gen_assembly(self, s):
		substr = "not "+self.left.hook
		s = super().gen_assembly(s, substr)
		return s

class AND(Observer):
	def __init__(self, left, right):
		super().__init__(left, right)		
		self.label = 'AND'
		self.tag = 2
		self.left.pre, self.right.pre = self, self

	def gen_assembly(self, s):
		substr = "and "+self.left.hook+" "+self.right.hook
		s = super().gen_assembly(s, substr)
		return s

class GLOBAL(Observer):
	def __init__(self, left, ub, lb=0):
		super().__init__(left)
		self.label = 'GLOBAL'
		self.tag = 3
		self.lb, self.ub = lb, ub
		self.left.pre = self

	def gen_assembly(self, s):
		if(self.lb==0):
			substr = "boxbox "+self.left.hook+" "+str(self.ub)
		else:
			substr = "boxdot "+self.left.hook+" "+str(self.lb)+" "+str(self.ub)
		s = super().gen_assembly(s, substr)
		return s

class UNTIL(Observer):
	def __init__(self, left, right, ub, lb=0):
		super().__init__(left, right)
		self.label = 'UNTIL'
		self.tag = 4
		self.lb, self.ub = lb, ub
		self.left.pre, self.right.pre = self, self

	def gen_assembly(self, s):
		substr = "until "+self.left.hook+" "+self.right.hook+" "+str(self.lb)+" "+str(self.ub)
		s = super().gen_assembly(s, substr)
		return s


