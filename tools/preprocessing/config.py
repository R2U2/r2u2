# DATA_WIDTH = 32 # sensor data width
SENSOR_DATA_WIDTH = 19
NUM_OF_SENSOR = 2
LOG_DATA_WIDTH = NUM_OF_SENSOR*SENSOR_DATA_WIDTH # total sensor data width

# Assembler output
MEM_FILE = 'tmp.ftm'
MEMINT_FILE = 'tmp.fti' 

# UART Data Conversion -> gen_uart_data.py
SETUP_DATA_WIDTH_extend_byte = 5 # do not modify!
SETUP_ADDR_WIDTH_extend_byte = 2 # do not modify!
DATA_BYTE_WIDTH_extend_byte =  (LOG_DATA_WIDTH-1)//8+1# combined sensor data width (byte)

# atomic checker -> assert_convert.py
CHECKER_INPUT_FILE = 'input.ast'
CHECKER_OUTPUT_FILE = 'res.atc'
CHECKER_ADDRESS_WIDTH = 11

# Generate logged data from simulation and test -> gen_log_data.py
DATA_WIDTH = LOG_DATA_WIDTH

# ser.py
TIMESTAMP_BYTE_extend_byte = 2
SERIAL_RUN_MODE = 'read_log'# select from one of: 1) self_sensing, 2) read_log, 3) type_input
UART_FILE = 'send.uart'# configuration file in uart byte format

# gen_log_data.py
SENSOR_DATA_FILE = 'sensor_data.dat'
LOG_DATA_FILE = 'logged_data.datb'
DATA_SAMPLE_NUMBER = 10 # total time stamp of sensor data you want to test in read_log mode
