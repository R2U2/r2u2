import sys
import os

# default config values
data = {'N_SIGS'         : 256,
        'N_ATOMICS'      : 256,
        'N_INSTRUCTIONS' : 256,
        'N_AT'           : 256,
        'N_INTERVAL'     : 128,
        'N_SETS'         : 0,
        'L_OPC'          : 5,
        'L_OP'           : 10,
        'L_INTVL'        : 8,
        'L_SCRATCH'      : 7,
        'L_COMP'         : 3,
        'L_FILTER'       : 4,
        'L_NUM'          : 32,
        'L_INTERVAL'     : 32,
        'N_INTERVAL'     : 128,
        'L_SCQ_SIZE'     : 1024,
        'L_SCQ_ADDRESS'  : 16,
        'L_DOT_BUFFER'   : 64,
        'N_PT_QUEUES'    : 128,
        'TL_INF'         : 32767*32767,
        'MAX_LINE'       : 128,
        'L_VARIABLE'     : 8,
        'N_FORMULAS'     : 64}

def parse_config(filename):
    try:
        with open(filename, 'r') as f:
            s = f.read()
    except FileNotFoundError:
        print('NOTE: Could not open configuration file, using default values')
        return
    #split input text into lines
    lines = s.splitlines()
    for line in lines:
        # check for comment and format line
        comment = line.find('#')
        if comment >= 0:
            line = line[0:comment]
        line = line.strip()
        if len(line) == 0:
            continue
        #split line into variable name and value
        v = line.split()
        if not len(v) == 2:
            print('Error: Invalid format of line ' + line)
            continue
        varname = v[0]
        value = v[1]
        #check variable name and add variable and value to dictionary is acceptable
        if varname in data.keys():
            data[varname] = value
        else:
            print("Error: Invalid variable name %s" % (str(varname)))

    return(data)

def check_updates(filename):
    try:
        with open(filename, 'r') as f:
            s = f.read()
    except FileNotFoundError:
        print('NOTE: R2U2Config.h file has been generated, recompilation is needed')
        return
    lines = s.splitlines()
    for line in lines:
        # format line
        line = line.strip()
        if len(line) == 0:
            continue
        #split line into macro name and value
        v = line.split()
        if not len(v) == 3:
            continue
        varname = v[1]
        value = v[2]
        # check if current value is different from new one
        if varname in data.keys() and str(data[varname]) != value:
            print('NOTE: R2U2Config.h file has been updated, recompilation is needed')
            return

def gen_config(filename):
    data['L_ATOMIC_ADDR'] = int.bit_length(int(data['N_ATOMICS'])-1)
    data['L_SIG_ADDR'] = int.bit_length(int(data['N_SIGS'])-1)
    data['L_SET_ADDR'] = int.bit_length(int(data['N_SETS'])-1)
    data['L_INSTRUCTION'] = int(data['L_OPC']) + int(data['L_OP']) + \
                            int(data['L_OP']) + int(data['L_INTVL']) + \
                            int(data['L_SCRATCH'])
    data['L_AT_INSTRUCTION'] = int(data['L_ATOMIC_ADDR']) + \
                               int(data['L_FILTER']) + int(data['L_SIG_ADDR']) \
                             + int(data['L_COMP']) + int(data['L_NUM']) + \
                               int(data['L_NUM']) + 1
    data['N_DOT_BUFFERS_TOTAL'] = int(data['N_PT_QUEUES']) * \
                                  int(data['L_DOT_BUFFER'])
    data['N_SUBFORMULA_SNYC_QUEUES'] = data['N_INSTRUCTIONS']

    header = '#ifndef R2U2_CONFIG_H\n' + \
             '#define R2U2_CONFIG_H\n\n'
    for key, val in data.items():
        header += '#define ' + key + ' ' + str(val) + '\n'
    header += 'typedef double r2u2_input_data_t;\n' + \
              'typedef unsigned int timestamp_t;\n' + \
              'typedef char signal_names[N_SIGS*L_VARIABLE];\n' + \
              'typedef char formula_names[N_FORMULAS*L_VARIABLE];\n' + \
              '\n#endif'

    with open(filename, 'w') as f:
        f.write(header)
