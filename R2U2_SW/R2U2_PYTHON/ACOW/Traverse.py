import re
# Travese the signal input and get output
class Traverse():
	def __init__(self, observer_seq, trace_file, isAtomic, output_file_name):
		self.observer_seq = observer_seq
		self.output_file_name = output_file_name
		self._file = trace_file
		self.isAtomic = isAtomic
		self.RTC = 0
		self.verify_result = []
		self.trace = []
		self.trace_name = []

	# Read the trace file, each signal in colom-wise format
	def construct_trace(self): 
		# s1 s2
		# 1   2
		# 2   3
		# 3   4
		l = re.compile(r'[ ,]+')
		line_cnt = 0
		lines = []
		with open(self._file, 'r') as handle:
			lines = handle.readlines()
		for line in lines:
			line = line.strip()
			if(line):
				if line_cnt == 0:
					self.trace_name = l.split(line)
				else:
					data_split = [float(i) for i in l.split(line)]
					self.trace.append(data_split)
				line_cnt+=1

	# map number to atomic, revise the mapping based on the MLTL formulae, column of the signal
	def s2a(self,signal_trace):	
		atomic_map = {}
		s2d = {signal_name:signal_trace[i] for i,signal_name in enumerate(self.trace_name)}
		
		##################################################################
		# For User: map boolean function to atomic
		atomic_map['a0'] = abs(s2d['s0'])<0.04
		atomic_map['a1'] = abs(s2d['s0'])<0.08
		atomic_map['a2'] = s2d['s1']>0.6
		##################################################################

		return atomic_map

	# if the input is atomic, no need to do atomic conversion. The signal name is the first line of the signal file
	def a2a(self,signal_trace):
		atomic_map = {}
		for i in self.trace_name:
			atomic_map[i] = signal_trace[0]==1
		return atomic_map

	def run(self):
		f = open(self.output_file_name,'w') # this file is used for regression test, where the result is written
		self.construct_trace()
		atconv = self.a2a if self.isAtomic else self.s2a
		for signal_trace in self.trace:
			atomic_map = atconv(signal_trace)
			f.write("\n----------TIME STEP: %d----------\n"%(self.RTC))
			for i, ob in enumerate(self.observer_seq):
				f.write("PC:%d "%(i))
				if(i==len(self.observer_seq)-1):
					if(ob.type=='ATOMIC'):						
						self.verify_result.append(ob.run(atomic_map,self.RTC,f))
					elif(ob.type=='BOOL'):
						self.verify_result.append(ob.run(self.RTC))

					else:
						self.verify_result.extend(ob.run(f))
				else:
					if(ob.type=='ATOMIC'):
						ob.run(atomic_map,self.RTC,f)
					elif(ob.type=='BOOL'):
						ob.run(self.RTC)
					else:
						ob.run(f)

			self.RTC += 1
		f.close()
		return self.verify_result