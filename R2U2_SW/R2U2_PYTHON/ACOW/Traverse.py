import re
from .MTLparse import *

# Travese the signal input and get output
class Traverse():
	def __init__(self, observer_seq, trace_file):
		self.observer_seq = observer_seq
		self._file = trace_file
		self.RTC = 0
		self.verify_result = []
		self.trace = []

	# Read the trace file
	def construct_trace(self):
		l = re.compile(r'[ ,]+')
		lines = []
		with open(self._file, 'r') as handle:
			lines = handle.readlines()
		for line in lines:
			data_split = [float(i) for i in l.split(line)];
			self.trace.append(data_split);

	# map number to atomic, revise the mapping based on the MLTL formulae, column of the signal
	def s2a(self,signal_trace):	
		atomic_map = {}
		alt = signal_trace[0]
		alt_vol = signal_trace[1]

		atomic_map['a0'] = abs(alt)<0.04
		atomic_map['a1'] = abs(alt)<0.08
		atomic_map['a2'] = abs(alt)<0.2
		atomic_map['a3'] = abs(alt_vol) > 0.6
		atomic_map['a4'] = alt>1.0

		return atomic_map

	def run(self):
		self.construct_trace()
		for signal_trace in self.trace:
			atomic_map = self.s2a(signal_trace)

			for i in range(len(self.observer_seq)):
				observer = self.observer_seq[i]
				if(i==len(self.observer_seq)-1):
					if(observer.type=='ATOMIC'):
						self.verify_result.append(observer.run(atomic_map,self.RTC))
					else:
						self.verify_result.extend(observer.run())
				else:
					if(observer.type=='ATOMIC'):
						observer.run(atomic_map,self.RTC)
					else:
						observer.run()
			self.RTC += 1
		return self.verify_result