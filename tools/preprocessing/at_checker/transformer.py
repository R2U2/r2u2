#!/usr/bin/python

from inputs import *
import sys

# minLen = sys.maxint # python 2
minLen = sys.maxsize # python 3
startTimestamp = 0
commonWidth = 0;

# r = ""		# generation report
# r = r + "input samples:\n"

# # read inputs
for i in inputFiles:		
	commonWidth = commonWidth + i.commonWidth 
# generate VHDL code

aCConfig = AtCheckerConfig()

r=""

r = r + "log data input width: " + str(commonWidth) + "\n"
r = r + "atmomics width: " + str(aCConfig.count) + "\n"

# generate vhdl package
offset = commonWidth
header = ""
body = ""
for i in inputFiles:
	for c in i.config:
		offset, f, h = c.generateVHDLFunction(commonWidth, offset)
		header = header + h + "\n"
		body = body + f + "\n"
		
p = ""
p = p + "library ieee;\n"
p = p + "use ieee.std_logic_1164.all;\n"
p = p + "use ieee.numeric_std.all;\n\n"
p = p + "package log_input_pkg is\n"
p = p + "    constant ATOMICS_WIDTH : integer := " + str(aCConfig.count) + ";\n"
p = p + "    constant ATC_ADDR_WIDTH : integer := 11;\n";
p = p + "    constant ATC_DATA_WIDTH : integer := 32;\n";
p = p + "    constant LOG_DATA_WIDTH : integer := " + str(commonWidth) + ";\n\n";

p = p + "    component at_checkers is\n"
p = p + "        port(\n"
p = p + "            clk          : in std_logic;\n"
p = p + "            rst_n        : in std_logic;\n"
p = p + "            config_addr  : in std_logic_vector(11-1 downto 0);\n"
p = p + "            config_data  : in std_logic_vector(32-1 downto 0);\n"
p = p + "            config_write : in std_logic;\n"
p = p + "            sample_clk   : in std_logic;\n"
p = p + "            data         : in std_logic_vector(LOG_DATA_WIDTH-1 downto 0);\n"
p = p + "            atomics      : out std_logic_vector(ATOMICS_WIDTH-1 downto 0)\n"
p = p + "        );\n"
p = p + "    end component;\n\n"
p = p +  header
p = p + "end log_input_pkg;\n\n"
p = p + "package body log_input_pkg is\n"
p = p + body
p = p + "end package body;\n"

writeToFile("log_input_pkg.vhd", p)

# generate atCheckers module

a = ""
a = a + "library ieee;\n"
a = a + "use ieee.std_logic_1164.all;\n"
a = a + "use ieee.numeric_std.all;\n"
a = a + "use work.at_checker_pkg.all;\n"
a = a + "use work.log_input_pkg.all;\n"
a = a + "--use work.filter_pkg.all;\n\n"

a = a + "entity at_checkers is\n"
a = a + "    port(\n"
a = a + "        clk          : in std_logic;\n"
a = a + "        rst_n        : in std_logic;\n"
a = a + "        config_addr  : in std_logic_vector(11-1 downto 0);\n"
a = a + "        config_data  : in std_logic_vector(32-1 downto 0);\n"
a = a + "        config_write : in std_logic;\n"
a = a + "        sample_clk   : in std_logic;\n"
a = a + "        data         : in std_logic_vector(LOG_DATA_WIDTH-1 downto 0);\n"
a = a + "        atomics      : out std_logic_vector(ATOMICS_WIDTH-1 downto 0)\n"
a = a + "    );\n"
a = a + "end entity;\n\n"

a = a + "architecture arch of at_checkers is\n"

# generate input signals
for i in inputFiles:
	for c in i.config:
		a = a + "    signal " + alignTo(c.name, 20) + " : std_logic_vector(" + str(c.width) + "-1 downto 0);\n"

a = a + "\n"

# generate filters
filters, filterSignals = aCConfig.generateVHDLFilters() 

# generate write signals
for i in range(0, aCConfig.count):
	a = a + "    signal write" + str(i) + " : std_logic;\n"

a = a + "\n"
a = a + filterSignals
a = a + "\n"

a = a + "begin\n"

# connect input signals
for i in inputFiles:
	for c in i.config:
		a = a + "    " + alignTo(c.name, 20) + " <= get_" + c.name + "(data);\n"

a = a + "\n"

r = r + "atChecker configuration:\n"

# write signals
a = a + "    process(config_write, config_addr) is\n"
a = a + "    begin\n"
for i in range(0, aCConfig.count):
	a = a + "        write" + str(i) + " <= '0';\n"

a = a + "\n"
a = a + "        case config_addr(11-1 downto 3) is\n"
for i in range(0, aCConfig.count):
	a = a + "            when \"" + toBinary(i, 8) + "\" =>\n"
	a = a + "                write" + str(i) + " <= config_write;\n"

a = a + "            when others =>\n"
a = a + "                null;\n"
a = a + "        end case;\n\n"

a = a + "    end process;\n\n"

# filter instances
a = a + filters

# instantiate atCheckers
at, rt = aCConfig.generatVHDLInstances()

a = a + at
r = r + rt

a = a + "end architecture;"

writeToFile("at_checkers.vhd", a)
writeToFile("report.txt", r)
print(r)

#print binary
#print p
#print a

