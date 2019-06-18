#!/usr/bin/python
"""
Simple script to convert assertion to binary.
e.g. 
16;-2;0;ADD;GRE
-12;0;0;DIF;EQU

Corresponding Hardware Component: at_checkers.vhd, at_checker.vhd.
"""
from config import CHECKER_INPUT_FILE as in_file,\
CHECKER_OUTPUT_FILE as dest_file,\
CHECKER_ADDRESS_WIDTH as ADDRESS_WIDTH,\
SENSOR_DATA_WIDTH as DATA_WIDTH

# Configuration
# in_file = 'input.ast'
# dest_file = 'res.atc'

### Don't modify anything below the line ###
####################################################


R_COMPARATOR ={
	'GEQ' : '000',#>=
	'LEQ' : '001',#<=
	'GRE' : '010',#>
	'LES' : '011',#<
	'NEQ' : '100',#!=
	'EQU' : '101'#==
}

A_OPERATOR ={
	'ADD' : '00',#a+b
	'SUB' : '01',#a-b
	'DIF' : '10',#|a-b|
}

res = ''
line_cnt = 0

d2b = lambda x: bin(int(x)&(2**DATA_WIDTH)-1)[2:] if int(x)<0 else bin(int(x))[2:].zfill(DATA_WIDTH)

def _get_constant(s):
	return '000\n'+d2b(s)+'\n'

def _get_shift_1(s):
	return '001\n'+d2b(s)+'\n'

def _get_shift_2(s):
	return '010\n'+d2b(s)+'\n'

def _get_operator(s):
	return '011\n'+A_OPERATOR[s].zfill(DATA_WIDTH)+'\n'

def _get_comparator(s):
	return '100\n'+R_COMPARATOR[s].zfill(DATA_WIDTH)+'\n'

with open(in_file) as f:
	for line in f:
		# s_config_addr signal & config_data signal
		checker_num = "{0:b}".format(line_cnt).zfill(ADDRESS_WIDTH-3)	    
		word = [x.strip() for x in line.split(';')]
		res += checker_num+_get_constant(word[0])
		res += checker_num+_get_shift_1(word[1])
		res += checker_num+_get_shift_2(word[2])
		res += checker_num+_get_operator(word[3])
		res += checker_num+_get_comparator(word[4])
		line_cnt += 1

with open(dest_file,'w+') as f:
	f.write('# Auto Generated Configuration Byte File for UART\n') 
	f.write(res) 


