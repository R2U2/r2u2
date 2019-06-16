from util import *

# input from log files

class APS(CsvParser):
	def __init__(self):
		CsvParser.__init__(self)
		self.file = "cpds_20120804_0750/DGPS_0.csv"
		
		self.addConfig(1, "", 0, 19, "APS1", "radius")
		self.addConfig(2, "", 0, 19, "APS2", "radius")
		
class TriM(CsvParser):
	def __init__(self):
		CsvParser.__init__(self)
		self.file = "cpds_20120804_0750/TriM_0.csv"
		
		# self.addConfig(2, "float", 2, 8, "battery_volatage", "in V")
		# self.addConfig(4, "float", 3, 32, "last_msg_time", "in ms")
		
#inputFiles = [Dgps(), TriM()]
inputFiles = [APS()]
SAMPLE_PERIOD = 100				# in seconds

# at checker generation

class AtCheckerConfig(AtChecker):
	def __init__(self):
		AtChecker.__init__(self)
		
		#self.add("dgps_height", "", 3, "moving_max-8", "", "rate", "")
		#self.add("last_msg_time", "", 1)
		self.add("APS1","APS2",2,"","","","")

		