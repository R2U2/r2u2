import sys
import os

# default config values
data = {'N_SIGS'     : 256,
        'N_ATOMICS'  : 256,
        'N_TL'       : 256,
        'N_AT'       : 256,
        'N_INTERVAL' : 128}

def parse_config(s):
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

def check_updates(s):
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

def main():

    print('Generating configuration files')

    try:
        with open(sys.argv[1], 'r') as f:
            s = f.read()
        parse_config(s) # will return updated data based on config file
    except FileNotFoundError:
        print('Warning: Could not open configuration file, using default values')

    try:
        with open(sys.argv[2], 'r') as f:
            s = f.read()
        check_updates(s) # read current .h file and notify user of changes
    except FileNotFoundError:
        pass

    header = '#ifndef R2U2_CONFIG_H\n' + \
             '#define R2U2_CONFIG_H\n\n'
    for key, val in data.items():
        header += '#define ' + key + ' ' + str(val) + '\n'
    header += '\n#endif'

    with open(sys.argv[2], 'w') as f:
        f.write(header)

if __name__ == '__main__':
    main()
