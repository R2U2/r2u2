#!/usr/bin/python

import time
import serial

# define auto_run
# auto run will periodically feed each data into the FPGA
auto_run = True # change this to False if you want to manually send sensor data to FPGA
log_data_file = 'logged_data.dat'
sample_period = 2 # Only works under auto_run=True. Period that FPGA send the sensor data. This data should >= wait_FPGA_time!


# configuration file in uart byte format
UART_FILE = 'send.uart'

### Modify the following parameters according to R2U2_pkg.vhd ###
DATA_BYTE_WIDTH_extend_byte = 6

wait_FPGA_time = 1 # wait FPGA finish send result (s)

#################################################################
# Configure the serial connections (the parameters differs on the device you are connecting to)
# By default, it is configured as 9600 8IN1
ser = serial.Serial(
    port='/dev/ttyUSB1',
    timeout=0,
    # baudrate=9600,
    # parity=serial.PARITY_ODD,
    # stopbits=serial.STOPBITS_TWO,
    # bytesize=serial.SEVENBITS
 )

### DON'T MODIFY CODE BELOW ###

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
    for i in range(0,len(uart_out),12):
        instruction_res=uart_out[i:i+12]
        content_cnt = 0
        for j in range(0,12,4):
            content_cnt += 1
            content = instruction_res[j:j+4]
            combined = int(content[3]+content[2]+content[1]+content[0],16)
            if content_cnt ==1:
                pc = combined
            elif content_cnt ==2:
                verdict = True if combined==1 else False
            elif content_cnt == 3:
                timestamp = combined
            else:
                content_cnt = 0
            
        print('PC:{0} = ({1},{2})').format(pc,verdict,timestamp)


ser.isOpen()
print(ser.name+' is open.')

print('Sending ATOMIC CHECKER, MONITOR configuration file......')
for i in config:
    ser.write(bits_to_hex(i).decode('hex'))
time.sleep(2)
print('Configuration complete!\n')


input=1
time_cnt = 0

if not auto_run:
    print ('Enter log data in binary format.\r\n(Insert "exit" to leave the application.)\n')
    while 1 :
        correct_format = True
        correct_size = True
        # get keyboard input
        input = raw_input("data>> ")
            # Python 3 users
            # input = input(">> ")
        output = []
        if input == 'exit':
            ser.close()
            exit()
        else:
            # check input correctnedd
            for i in input:
                if(i not in ('0','1')):
                    correct_format = False
            if len(input)>DATA_BYTE_WIDTH_extend_byte*8:
                correct_size = False
            if(not correct_format):
                print('Input is not in binary format, type again.\n')
                continue
            if(not correct_size):
                print('Size is larger than {0} bits, try again:\n').format(DATA_BYTE_WIDTH_extend_byte*8)
                continue
            # send the character to the device
            splitted = split_to_byte(input,DATA_BYTE_WIDTH_extend_byte)
            for i in splitted:
                input = bits_to_hex(i).decode('hex')
                ser.write(input)
            # wait before reading output (let's give device time to answer)
            time.sleep(wait_FPGA_time)
            print("----------TIME STEP: {0}----------").format(time_cnt)
            time_cnt += 1
            while ser.inWaiting() > 0:
                res = ser.read(1).encode('hex')
                output.append(res)

            decode_uart_out(output)
            print('')
else:
    logged_data = []
    with open(log_data_file) as f:
        for line in f:
            line = line.strip()
            if not line or line[0]=='#':
                continue
            logged_data.append(line)

    for i in logged_data:
        print("data>> "+i)
        output = []
        # send the character to the device
        splitted = split_to_byte(i,DATA_BYTE_WIDTH_extend_byte)
        for i in splitted:
            input = bits_to_hex(i).decode('hex')
            ser.write(input)
        # wait before reading output (let's give device time to answer)
        time.sleep(wait_FPGA_time)
        print("----------TIME STEP: {0}----------").format(time_cnt)
        time_cnt += 1
        while ser.inWaiting() > 0:
            res = ser.read(1).encode('hex')
            output.append(res)

        decode_uart_out(output)
        print('')
        time.sleep(sample_period-wait_FPGA_time)

    print('Finish sending all the data with period {0} s'.format(sample_period))
    ser.close()
    exit()
