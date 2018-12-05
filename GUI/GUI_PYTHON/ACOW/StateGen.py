# ------------------------------------------------------------
# StateGen.py
# ----------------------------------
# Enumerate all the state given variables
# ----------------------------------
# Author: Pei Zhang
# ------------------------------------------------------------
class StateGen():
	totNum = 0
	def __init__(self, varNum, statePrefix, atomicPrefix):
		assert varNum > 0 , 'varNum should be greater than 0'
		self.varNum = varNum
		self.statePrefix, self.atomicPrefix = statePrefix, atomicPrefix
		StateGen.totNum = 0

	def gen_aut(self):
		m_state, m_trans = {}, {}
		m_all_state = set()
		self.gen_helper(0,[],m_state)
		for i in range(StateGen.totNum):
			m_all_state.add(self.statePrefix+str(i))
		for i in range(StateGen.totNum):
			m_trans[self.statePrefix+str(i)] = m_all_state
		return m_state, m_trans

	def gen_helper(self, depth, ls, m):
		if depth == self.varNum:
			atomicMap = {}
			for i in range(self.varNum):
				atomicMap[self.atomicPrefix+str(i)] = ls[i]
			m['s'+str(StateGen.totNum)] = atomicMap
			StateGen.totNum += 1
			return
		for prop in (0,1):
			ls.append(prop)
			self.gen_helper(depth+1, ls, m)
			ls.pop()