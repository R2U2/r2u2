from util import *

# input from log files

class APS(CsvParser):
	def __init__(self):
		CsvParser.__init__(self)
		self.file = ""
		
		self.addConfig(1, "", 0, 19, "APS1", "radius")
		self.addConfig(2, "", 0, 19, "APS2", "radius")
		
#inputFiles = [Dgps(), TriM()]
inputFiles = [APS()]

# at checker generation
class AtCheckerConfig(AtChecker):
	def __init__(self):
		AtChecker.__init__(self)
		
		#self.add("dgps_height", "", 3, "moving_max-8", "", "rate", "")
		#self.add("last_msg_time", "", 1)
		self.add("APS1","APS2",2,"","","","")

		