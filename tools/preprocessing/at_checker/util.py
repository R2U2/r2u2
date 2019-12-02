
# import fileinput
# import matplotlib
# from matplotlib.backends.backend_pdf import PdfPages
# import pylab

def onescomp(binstr):
    return ''.join('1' if b=='0' else '0' for b in binstr)

def twoscomp(binstr):
    return bin(int(onescomp(binstr),2)+1)[2:]

def toBinary(value, width):
	b = bin(value)[2:]
	
	if value >= 0:
		while len(b) < width:
			b = "0" + b
			
	else:
		b = twoscomp("0" + bin(-value)[2:])
		while len(b) < width:
			b = "1" + b
	
	if len(b) > width:	
		print(value, "Error: does not fit into", width, "bits")
		b = b[0:width] 
		
	return b

class ParserConfigItem:
	def __init__(self, channel, type, comma, width, name, comment):
		self.channel = channel
		self.type = type
		self.comma = comma
		self.width = width
		self.name = name
		self.comment = comment
		
	def generateVHDLFunction(self, inWidth, offset):
		f = ""
		
		f = f + "    -- " + self.name + " " + self.comment + "\n"
		f = f + "    function get_" + self.name + " (input : std_logic_vector(" + str(inWidth) + "-1 downto 0)) return std_logic_vector is\n"
		f = f + "    begin\n" 
		f = f + "        return input(" + str(offset) + "-1 downto " + str(offset - self.width) + ");\n"
		f = f + "    end function;\n"
		
		h = ""
		h = h + "    -- " + self.name + " " + self.comment + "\n"
		h = h + "    constant " + self.name.upper() + "_WIDTH : integer := " + str(self.width) + ";\n"
		h = h + "    function get_" + self.name + " (input : std_logic_vector(" + str(inWidth) + "-1 downto 0)) return std_logic_vector;\n"
		
		return [offset - self.width, f, h]
	
	
class CsvParser:
	def __init__(self):
		self.config = []
		self.__data = []
		self.firstTimestamp = 0
		self.commonWidth = 0
	
	def addConfig(self, channel, type, comma, width, name, comment):
		self.config.append(ParserConfigItem(channel, type, comma, width, name, comment))
		self.commonWidth = self.commonWidth + width
		
class AtCheckerConfigItem:
	def __init__(self, input1, input2, count, filter1, filter2, rate1, rate2):
		self.input1 = input1
		self.input2 = input2
		self.count = count
		self.filter1 = filter1
		self.filter2 = filter2
		self.rate1 = rate1
		self.rate2 = rate2
		
class AtChecker:
	def __init__(self):
		self.config = []
		self.count = 0;
		
	def add(self, input1, input2, count, filter1, filter2, rate1, rate2):
		self.config.append(AtCheckerConfigItem(input1, input2, count, filter1, filter2, rate1, rate2))
		self.count = self.count + count
		
	def generateVHDLIdentifier(self, name):
		return name.replace("-", "_")
		
	def generateVHDLFilter(self, filter, signalName, signalWidth):
		f = ""	# instances
		s = ""  # signals
		
		if filter != "":
			c = filter.split("-")
			
			filterName = self.generateVHDLIdentifier(filter)
				
			if c[0] == "max":
				f = f + "    " + signalName + "_" + filterName + " : max\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			if c[0] == "min":
				f = f + "    " + signalName + "_" + filterName + " : min\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			elif c[0] == "lowpass":
				f = f + "    " + signalName + "_" + filterName + " : lowpass\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH,\n"
				f = f + "        FILTER_LEN => " + str(c[1]) + ",\n"
				f = f + "        FILTER_WEIGHT => " + str(c[2]) + "\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			elif c[0] == "moving_min":
				f = f + "    " + signalName + "_" + filterName + " : moving_min\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH,\n"
				f = f + "        FILTER_LEN => " + str(c[1]) + "\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			elif c[0] == "moving_max":
				f = f + "    " + signalName + "_" + filterName + " : moving_max\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH,\n"
				f = f + "        FILTER_LEN => " + str(c[1]) + "\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			elif c[0] == "moving_avg":
				f = f + "    " + signalName + "_" + filterName + " : moving_avg\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH,\n"
				f = f + "        FILTER_LEN => " + str(c[1]) + "\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			elif c[0] == "rate":
				f = f + "    " + signalName + "_" + filterName + " : rate\n"
				f = f + "    generic map(\n"
				f = f + "        DATA_WIDTH => " + signalWidth.upper() + "_WIDTH\n"
				f = f + "    )\n"
				f = f + "    port map (\n"
				f = f + "        clk   => clk,\n"
				f = f + "        rst_n => rst_n,\n"
				f = f + "        sample_clk => sample_clk,\n"
				f = f + "        data_in => " + signalName + ",\n"
				f = f + "        data_out => " + signalName + "_" + filterName + "_filtered\n"
				f = f + "    );\n\n"
				
			s = s + "    signal " + signalName + "_" + filterName + "_filtered : std_logic_vector(" + signalWidth.upper() + "_WIDTH-1 downto 0);\n"
					
		return [f, s]
		
	def generateVHDLFilters(self):
		f = ""	# instances
		s = ""  # signals
		
		for c in self.config:
			filter, signals = self.generateVHDLFilter(c.filter1, c.input1, c.input1)
			f = f + filter
			s = s + signals
			filter, signals = self.generateVHDLFilter(c.filter2, c.input2, c.input2)
			f = f + filter
			s = s + signals
			filter, signals = self.generateVHDLFilter(c.rate1, c.input1 + "_" + self.generateVHDLIdentifier(c.filter1) + "_filtered", c.input1)
			f = f + filter
			s = s + signals
			filter, signals = self.generateVHDLFilter(c.rate2, c.filter2 + "_" + self.generateVHDLIdentifier(c.filter1) + "_filtered", c.input2)
			f = f + filter
			s = s + signals
					
		return [f, s]
		
	def generatVHDLInstances(self):
		a = ""	# instance
		r = ""	# report
		number = 0
		
		for c in self.config:
			for i in range(0, c.count):
				a = a + "    atc_" + str(number) + " : at_checker\n"
				a = a + "    generic map (\n"
				a = a + "        IN_1_WIDTH => " + c.input1.upper() + "_WIDTH,\n"
				if c.input2 == "":
					a = a + "        IN_2_WIDTH => 1,\n"
				else:
					a = a + "        IN_2_WIDTH => " + c.input2.upper() + "_WIDTH,\n"
				a = a + "        ADDR       => " + str(number) + "\n"
				a = a + "    )\n"
				a = a + "    port map(\n"
				a = a + "        clk   => clk,\n"
				a = a + "        rst_n => rst_n,\n"
				a = a + "        config_addr  => config_addr(3-1 downto 0),\n"
				a = a + "        config_data  => config_data,\n"
				a = a + "        config_write => write" + str(number) + ",\n"
				if c.filter1 == "":
					a = a + "        in1   => " + c.input1 + ",\n"
				else:
					if c.rate1 == "":
						a = a + "        in1   => " + c.input1 + "_" + self.generateVHDLIdentifier(c.filter1) + "_filtered,\n"
					else:
						a = a + "        in1   => " + c.input1 + "_" + self.generateVHDLIdentifier(c.filter1) + "_filtered_" + self.generateVHDLIdentifier(c.rate1) + "_filtered,\n"
				if c.input2 == "":
					a = a + "        in2   => \"0\",\n"
				else:
					if c.filter2 == "":
						a = a + "        in2   => " + c.input2 + ",\n"
					else:
						if c.rate2 == "":
							a = a + "        in2   => " + c.input2 + "_" + self.generateVHDLIdentifier(c.filter2) + "_filtered,\n"
						else:	
							a = a + "        in2   => " + c.input2 + "_" + self.generateVHDLIdentifier(c.filter2) + "_filtered_" + self.generateVHDLIdentifier(c.rate2) + "_filtered,\n"
				a = a + "        ap    => atomics(" + str(number) + ")\n"
				a = a + "    );\n\n"
				
				r = r + "    atChecker " + str(number) + ":\n"
				r = r + "        in1: " + c.input1 + " (filter: " + c.filter1 + " " + c.rate1 + ")\n"
				r = r + "        in2: " + c.input2 + " (filter: " + c.filter2 + " " + c.rate2 + ")\n"
				
				number = number + 1
				
		return [a, r]
		
def writeToFile(file, content):
	f = open(file, 'w')
	f.write(content)
	f.close

def alignTo(string, cols):
	while len(string) < cols:
		string = string + " "
		
	return string
