#!/usr/bin/python
from config import SETUP_DATA_WIDTH_extend_byte, SETUP_ADDR_WIDTH_extend_byte, DATA_BYTE_WIDTH_extend_byte
from config import SERIAL_RUN_MODE as RUN_MODE,\
					UART_FILE as dest_file,\
					CHECKER_OUTPUT_FILE as atc_in_file,\
					MEM_FILE as mem_in_file,\
					MEMINT_FILE as int_in_file,\
					LOG_DATA_FILE as log_data_file

general_config_info_byte = 1 # don't modify this.
'''
The data sarts with 3 general configuration info data
0: number of at_checker address to configure
1: number of future time instruction to configure
2: number of future time interval to configure 
Each of them with size <general_config_info_byte> byte
'''
# .atc sample
# 00000000000
# 00000000000000000000000000010000
# 00000000001
# 11111111111111111111111111111110
# 00000000010
# 00000000000000000000000000000000
# 00000000011
# 00000000000000000000000000000000
# 00000000100
# 00000000000000000000000000000010
# 00000001000
# 11111111111111111111111111110100
# 00000001001
# 00000000000000000000000000000000
# 00000001010
# 00000000000000000000000000000000
# 00000001011
# 00000000000000000000000000000010
# 00000001100
# 00000000000000000000000000000101

# .ftm sample
# 1110000000000010000000000000000000000000
# 1011010000000000000000000000000000000000
# 1110000000000010000000000000000000000000
# 1110000000000000000000000000000000000000
# 1101010000000101000000011000000010000000
# 1010110000000011000000100000000000000000
# 1111110000001010000000000000000000000000

# .fti sample
# 0000000000000000000000000000000000000000000000000000000000000100
# 0000000000000000000000000000010100000000000000000000000000001010

#### Don't modify anything below the line ####
#################################################################
def split_to_byte(intput_binary,num_of_bytes):
	temp = bin(int(intput_binary,2))[2:].zfill(num_of_bytes*8)
	split = [str(temp[i-8:i]) for i in range(len(temp),0,-8)]
	return split
	
def split_dec_to_byte(intput_decimal,num_of_bytes):
	temp = bin(int(intput_decimal))[2:].zfill(num_of_bytes*8)
	split = [str(temp[i-8:i]) for i in range(len(temp),0,-8)]
	return split


res = []

atc_cnt,mem_cnt,int_cnt = 0,0,0
is_set_up_data = False
with open(atc_in_file) as f:
	for line in f:
		line = line.strip()
		if not line or line[0]=='#':
			continue
		if is_set_up_data:
			res+=split_to_byte(line,SETUP_DATA_WIDTH_extend_byte)
		else:
			res+=split_to_byte(line,SETUP_ADDR_WIDTH_extend_byte)
		atc_cnt += 1
		is_set_up_data = not is_set_up_data 
atc_cnt/=2

for file in (mem_in_file,int_in_file):
	line_cnt = 0
	with open(file) as f:
		for line in f:
			line = line.strip()
			if not line or line[0]=='#':
				continue
			res+=split_to_byte(line,SETUP_DATA_WIDTH_extend_byte)
			line_cnt += 1
	if file == mem_in_file:
		mem_cnt = line_cnt
	else:
		int_cnt = line_cnt


mode_line = 0
if(RUN_MODE in ('read_log','type_input')):
	mode = 0
elif(RUN_MODE == 'self_sensing'):
	mode = 1


res = split_dec_to_byte(mode,general_config_info_byte)+ split_dec_to_byte(atc_cnt,general_config_info_byte)+\
	split_dec_to_byte(mem_cnt,general_config_info_byte)+split_dec_to_byte(int_cnt,general_config_info_byte)+res

# write output
with open(dest_file,'w+') as f:
	f.write('# Auto Generated R2U2 Configuration Byte File for UART Transmission.\n') 
	for eachline in res:
		f.write("%s\n" % eachline) 
