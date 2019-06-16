#!/usr/bin/python

from config import SENSOR_DATA_WIDTH
from config import SENSOR_DATA_FILE as sensor_data_file,\
					LOG_DATA_FILE as dest_file,\
					DATA_SAMPLE_NUMBER as each_sample_number
#SENSOR_DATA_WIDTH = 32 # the bit width of each data

# sensor_data_file = 'sensor_data.dat'
# dest_file = 'logged_data.dat'

# each_sample_number = 10 # how many sample period data

"""
sensor_data.dat format
# sensor 0
12,12,45,12,43,12,65,13,131,215,10,11,95,23
# sensor 1
23,12,53,1,2,54,1,3,0,12,0,0,0,0,0,0,0,0,0 
"""

result = ["" for n in range(each_sample_number)]

def split_dec_to_byte(intput_decimal):
	temp = bin(int(intput_decimal))[2:].zfill(SENSOR_DATA_WIDTH)
	return str(temp)
	
with open(sensor_data_file) as f:
	for line in f: # each line is 
		line = line.strip()
		if not line or line[0]=='#':
			continue
		sensorArr = line.split(',')	
		for i,each_sample in enumerate(sensorArr[:each_sample_number]):			
			result[i]+=split_dec_to_byte(each_sample)

with open(dest_file,'w+') as f:
	f.write('# Auto Generated Data Log File for UART') 
	for eachline in result:
		f.write("\n%s" % eachline) 
