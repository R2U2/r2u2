import sys
import os

# default config values
data = {'N_SIGS'     : 256,
        'N_ATOMICS ' : 256,
        'N_TL'       : 256,
        'N_AT'       : 256,
        'N_INTERVAL' : 128}

def parse_config(s, data):
    #list of acceptable variable names
    configvariables = ['N_SIGS','N_ATOMICS','N_TL','N_AT','N_INTERVAL']
    #split input text into lines
    lines = s.split('\n')
    for line in lines:
        print(line)
        #check for comment
        if line[0] == '#':
            continue
        #split line into variable name and value
        v = line.split()
        varname = v[0]
        value = v[1]
        #check variable name and add variable and value to dictionary is acceptable
        if varname in data.keys():
            data[varname] = value
        else:
            print("Invalid variable name: %s" % (str(varname)))
        return(data)

def main():

    print('Generating configuration files')

    try:
        with open(sys.argv[1], 'r') as f:
            s = f.read()
        parse_config(s, data) # will return updated data based on config file
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
