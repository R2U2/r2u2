#!/usr/bin/python

import time
import serial
from config import DATA_BYTE_WIDTH_extend_byte,TIMESTAMP_BYTE_extend_byte,UART_FILE
from config import SERIAL_RUN_MODE as run_mode
# auto run will periodically feed each data into the FPGA
# change this to False if you want to manually send sensor data to FPGA
# run_mode = 'read_log'# self_sensing, read_log, type_input

# configuration file in uart byte format
# UART_FILE = 'send.uart'

### Modify the following parameters according to R2U2_pkg.vhd ###
# DATA_BYTE_WIDTH_extend_byte = 8 # used in 'read_log' and 'type_input' mode
# TIMESTAMP_BYTE_extend_byte = 2



#################################################################
# Configure the serial connections (the parameters differs on the device you are connecting to)
# By default, it is configured as 9600 8IN1
ser = serial.Serial(
    port='/dev/ttyUSB0',
    timeout=0,
    baudrate=9600,
    # parity=serial.PARITY_ODD,
    # stopbits=serial.STOPBITS_TWO,
    # bytesize=serial.SEVENBITS
 )

### DON'T MODIFY CODE BELOW ###
begin_time = time.time()


def bits_to_hex(user8bit): # convert the 8-bit user input to hex
    numInt = int(user8bit, 2)
    strHex = hex(numInt)
    userHex = strHex[2:].zfill(2)
    # make sure the payload is a two-digit hex
    return userHex

def split_to_byte(intput_binary,num_of_bytes):
    temp = bin(int(intput_binary,2))[2:].zfill(num_of_bytes*8)
    split = [str(temp[i-8:i]) for i in range(len(temp),0,-8)]
    return split


with open(UART_FILE) as f:
    config = []
    for line in f:
        line = line.strip()
        if not line or line[0]=='#':
            continue
        config.append(line)

def decode_uart_out(uart_out):
    pc,verdict,timestamp = -1,False,-1
    for i in range(0,len(uart_out),TIMESTAMP_BYTE_extend_byte*3):
        instruction_res=uart_out[i:i+TIMESTAMP_BYTE_extend_byte*3]
        content_cnt = 0
        for j in range(0,TIMESTAMP_BYTE_extend_byte*3,TIMESTAMP_BYTE_extend_byte):
            content_cnt += 1
            # content = instruction_res[j:j+4]
            content = instruction_res[j:j+TIMESTAMP_BYTE_extend_byte]
            # combined = int(content[3]+content[2]+content[1]+content[0],16)
            sum = ''

            if(len(content)<TIMESTAMP_BYTE_extend_byte):# not enough data to decode
                print('Missing feedback data from UART.')
                return False

            for k in range(TIMESTAMP_BYTE_extend_byte):
                sum=content[k]+sum
            combined = int(sum,16)
            if content_cnt ==1:
                pc = combined
            elif content_cnt ==2:
                verdict = True if combined==1 else False
            elif content_cnt == 3:
                timestamp = combined
            else:
                content_cnt = 0
            
        print('PC:{0} = ({1},{2})').format(pc,verdict,timestamp)
    return True

ser.isOpen()
print(ser.name+' is open.')

print('Reseting R2U2......')
# for i in config:
#    ser.write(bits_to_hex(i).decode('hex'))
# time.sleep(0.05)
# print('Configuration complete!\n')


input=1
time_cnt = 0

if run_mode=='type_input':
    pass

elif(run_mode =='read_log'):
   pass

elif(run_mode =='self_sensing'):
 	input = bits_to_hex(bin(1)[2:].zfill(8)).decode('hex')
	ser.write(input)
	print('R2U2 Reset Complete!')

else:
    print('Run Mode Error!')
