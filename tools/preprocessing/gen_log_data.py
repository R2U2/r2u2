#!/usr/bin/python

from config import SENSOR_DATA_WIDTH
from config import SENSOR_DATA_FILE as sensor_data_file,\
					LOG_DATA_FILE as dest_file,\
					DATA_SAMPLE_NUMBER as each_sample_number
'''
SENSOR_DATA_WIDTH  : the bit width of each data
each_sample_number : how many sample period data
'''

"""
sensor_data.dat format
# sensor 0
12,12,45,12,43,12,65,13,131,215,10,11,95,23
# sensor 1
23,12,53,1,2,54,1,3,0,12,0,0,0,0,0,0,0,0,0 
"""

result = ["" for n in range(each_sample_number)]

d2b = lambda x: bin(int(x)&(2**SENSOR_DATA_WIDTH)-1)[2:] if int(x)<0 else bin(int(x))[2:].zfill(SENSOR_DATA_WIDTH)

with open(sensor_data_file) as f:
	for line in f: # each line is 
		line = line.strip()
		if not line or line[0]=='#':
			continue
		sensorArr = line.replace(' ',',').replace('	',',').split(',')	
		for i,each_sample in enumerate(sensorArr[:each_sample_number]):			
			result[i]+=str(d2b(each_sample))

with open(dest_file,'w+') as f:
	f.write('# Auto Generated Data Log File for UART (support negative signal)') 
	for eachline in result:
		f.write("\n%s" % eachline) 
