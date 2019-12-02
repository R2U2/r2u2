#!/usr/bin/python
#(requires python 2.7)
import time
import serial
from config import DATA_BYTE_WIDTH_extend_byte,TIMESTAMP_BYTE_extend_byte,UART_FILE
from config import SERIAL_RUN_MODE as run_mode
from config import DATA_SAMPLE_NUMBER as total_sample
from config import LOG_DATA_FILE as log_data_file

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

print('Sending ATOMIC CHECKER, MONITOR configuration file......')
for i in config:
    ser.write(bits_to_hex(i).decode('hex'))
time.sleep(0.05)
print('Configuration complete!\n')


input=1
time_cnt = 0

if run_mode=='type_input':
    wait_FPGA_time = 0.5 # wait FPGA finish send result (s)
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
            ############# newly added line for system reset function
            input = bits_to_hex(bin(1)[2:].zfill(8)).decode('hex')
            ser.write(input)
            ######################
            ser.close()
            exit()
        else:
            # check input correctness
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
                splitted_input = bits_to_hex(i).decode('hex')
                ser.write(splitted_input)
            # wait before reading output (let's give device time to answer)
            time.sleep(wait_FPGA_time)
            print("----------TIME STEP: {0}----------").format(time_cnt)
            time_cnt += 1
            while ser.inWaiting() > 0:
                res = ser.read(1).encode('hex')
                output.append(res)

            decode_uart_out(output)
            ############# newly added line for system reset function
            input = bits_to_hex(bin(0)[2:].zfill(8)).decode('hex')
            ser.write(input)
            ######################
            print('')

elif(run_mode =='read_log'):
    sample_period = 2 #Period that FPGA send the sensor data. This data should >= wait_FPGA_time!
    wait_FPGA_time = 0.5 # wait FPGA finish send result (s)
    logged_data = []
    with open(log_data_file) as f:
        for line in f:
            line = line.strip()
            if not line or line[0]=='#':
                continue
            logged_data.append(line)

    for idx,i in enumerate(logged_data):


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
        

        if(idx < total_sample-1):
            input = bits_to_hex(bin(0)[2:].zfill(8)).decode('hex')
            ser.write(input)
        else:
            input = bits_to_hex(bin(1)[2:].zfill(8)).decode('hex')
            print('R2U2 reset.')
            ser.write(input)
            ser.close()
            exit()
        
        time.sleep(sample_period-wait_FPGA_time)


    print('Finish sending all the data with period {0} s'.format(sample_period))
    ser.close()
    exit()

elif(run_mode =='self_sensing'):

    while(1):
        output = []
        print("----------TIME STEP: {0}----------").format(time_cnt)
        

        while ser.in_waiting == 0: # wait for first input
            pass
        res = ser.read(1).encode('hex')
        output.append(res)

        start_time = time.time()
        elapsed_time = time.time() - start_time
        while elapsed_time < 0.1: # elapsed_time must be smaller than sample/RTC period
            while ser.in_waiting > 0 :
                res = ser.read(1).encode('hex')
                output.append(res)
            elapsed_time = time.time() - start_time

        ############# newly added line for system reset function
        input = bits_to_hex(bin(0)[2:].zfill(8)).decode('hex')
        ser.write(input)
        ######################
        
        print('Natural Time: {0}(s)'.format(time.time()-begin_time))
        print(output)
        # if(decode_uart_out(output[:-8])): # if you want to check sensor data from uart, remove the suffix sensor data before decode 
        #     time_cnt += 1
        if(decode_uart_out(output)):
            time_cnt += 1
        print('')

else:
    print('Run Mode Error!')
