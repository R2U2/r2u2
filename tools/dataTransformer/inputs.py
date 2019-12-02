from util import *

# input from log files

class Dgps(CsvParser):
	def __init__(self):
		CsvParser.__init__(self)
		self.file = "cpds_20120805_0753/DGPS_0.csv"
		
		self.addConfig(4, "float", 0, 16, "dgps_height", "height in meters")
		self.addConfig(12, "float", 0, 8, "dgps_speed", "speed in meters per second")
		
class TriM(CsvParser):
	def __init__(self):
		CsvParser.__init__(self)
		self.file = "cpds_20120805_0753/TriM_0.csv"
		
		self.addConfig(2, "float", 2, 8, "battery_volatage", "in V")
		self.addConfig(4, "float", 3, 32, "last_msg_time", "in ms")
		
#inputFiles = [Dgps(), TriM()]
inputFiles = [Dgps()]
SAMPLE_PERIOD = 100				# in seconds

# at checker generation

class AtCheckerConfig(AtChecker):
	def __init__(self):
		AtChecker.__init__(self)
		
		self.add("dgps_height", "", 3, "moving_max-8", "", "rate", "")
		#self.add("last_msg_time", "", 1)
		