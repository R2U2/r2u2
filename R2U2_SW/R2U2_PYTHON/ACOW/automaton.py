"""
top level automaton class
{'s0',{'a0':1,'a1':0,'a2':1,'a3':1}} #s0:1011
"""
from graphviz import *

class state():
	def __init__(self, name, var = {}):
		self.name = name
		self.next = set()
		self.var = var

	def __repr__(self):
		return self.name

class automaton():

	def __init__(self):
		self.STATE = {}
		self.INITIAL_STATE = None
		self.DEST_STATE = None
		self.DELTA = None
		# map the state name to the state object
		self.state_map = {}

	def __repr__(self):
		return 'Total States: {0}\nState Lists: {1}\n'.format(len(self.STATE),[key for key in self.STATE])

	def init(self):
		for states, variables in self.STATE.items():
			cur_state = state(states)
			cur_state.var = variables
			self.state_map[states]=cur_state #map the state name to the state object

		for states, next_state in self.DELTA.items():
			self.state_map[states].next = [self.state_map[x] for x in next_state]
			#print(self.state_map[states].next)
			# for each_next_state in next_state:
			# 	self.state_map[states].next.append = self.state_map[each_next_state]

		self.INITIAL_STATE = self.state_map[self.INITIAL_STATE]
		self.DEST_STATE = self.state_map[self.DEST_STATE]

	def show(self):
		dot = Digraph(comment='State Space Graph')
		for states in self.STATE:
			color = 'grey'
			if states==self.INITIAL_STATE.name:
				color = 'green' # initial state color
			elif states==self.DEST_STATE.name:
				color = 'blue' # end state color
			dot.node(states,color=color,style='filled')
		
		for states, next_states in self.DELTA.items():
			for next_state in next_states:		
				dot.edge(states,next_state)
		dot.render('visual_output/ss.gv', view=True) 

