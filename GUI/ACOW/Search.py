# ------------------------------------------------------------
# search.py
# ----------------------------------
# Different search method
# ----------------------------------
# Author: Pei Zhang
# ------------------------------------------------------------
from random import shuffle
from .automaton import automaton
from .MTLparse import *
import logging, sys

# use level=logging.DEBUG to enable debug info
#logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)
logging.basicConfig(stream=sys.stderr, level=logging.CRITICAL)
class Search():
	def __init__(self, automaton, observer_seq, agent='DFS'):
		assert agent in ('DFS','DFS_FA','SED','DES'), 'Error: Agent not exist'
		self.agent = agent
		self.automaton = automaton
		self.observer_seq = observer_seq
		self.current_time = 0
		self.trace = []

	def backtrack(self):
		self.current_time -= 1
		for i in range(len(self.observer_seq)):
			observer = self.observer_seq[i]	
			observer.recede_status()

	def go_to_next_state(self,state):
		logging.debug('----------- Time: %d, State: %s ----------',self.current_time,state)
		for i in range(len(self.observer_seq)):
			observer = self.observer_seq[i]
			if(observer.type=='ATOMIC'):
				observer.run(state.var,self.current_time)
			else:
				observer.run()
		self.current_time += 1
		logging.debug('\n')


	def is_state_acceptable(self):
		top = self.observer_seq[len(self.observer_seq)-1]
		return top.return_verdict, top.has_output

	def run(self,path=None,max_step=200):
		if self.agent == 'DFS' or self.agent == 'DFS_FA':
			self.max_step = max_step
			if self.agent == 'DFS':
				finish,reach_max_step = self.dfs(self.automaton.INITIAL_STATE,0)
			else:
				finish,reach_max_step = self.dfs_fa(self.automaton.INITIAL_STATE,0)
			if(finish):
				if reach_max_step:
					print('Reach Maximum Searching Step',max_step)
				else:
					print('Find Feasible Track:',self.trace)
			else:
				print('No Feasible Track Found.')
		elif self.agent == 'SED':
			self.sed()
		else:
			self.des(path)

	# 'DES': Specify the path by ourselves
	def des(self,path):
		for state in path:
			self.go_to_next_state(self.automaton.state_map[state])

	# 'DFS': Depth first search
	# Return : (meet stop criterion?,reach max_step?)
	def dfs(self,current_state,step_len):
		if step_len == self.max_step:
			return True,True
		self.trace.append(current_state.name)
		self.go_to_next_state(current_state)
		if not self.is_state_acceptable()[0]:
			self.backtrack()
			del self.trace[-1]
			return False,False
		#elif current_state.name==self.automaton.DEST_STATE:
		elif current_state is self.automaton.DEST_STATE and self.is_state_acceptable()[1]:
			return True,False
		else:
			step_len += 1
			keys = [x for x in current_state.next]
			shuffle(keys)
			for state in keys:
				finish,reach_max_step = self.dfs(state,step_len)
				if(finish):
					return True,reach_max_step
			self.backtrack()
			del self.trace[-1]
			return False,False

	# 'Force Approaching DFS': Use depth first search, but force it to consider enter final state first
	# Return : (meet stop criterion?,reach max_step?)
	def dfs_fa(self,current_state,step_len):
		if step_len == self.max_step:
			return True,True
		self.trace.append(current_state.name)
		self.go_to_next_state(current_state)
		if not self.is_state_acceptable()[0]:
			self.backtrack()
			del self.trace[-1]
			return False,False
		#elif current_state.name==self.automaton.DEST_STATE:
		elif current_state is self.automaton.DEST_STATE and self.is_state_acceptable()[1]:
			return True,False
		else:
			step_len += 1
			keys = [x for x in current_state.next if x is not self.automaton.DEST_STATE]
			shuffle(keys)
			if self.automaton.DEST_STATE in current_state.next:
				keys = [self.automaton.DEST_STATE]+keys
			#print(keys)
			for state in keys:
				finish,reach_max_step = self.dfs_fa(state,step_len)
				if(finish):
					return True,reach_max_step
			self.backtrack()
			del self.trace[-1]
			return False,False

	# 'SED': Shortest edit distance
	def sed():
		pass