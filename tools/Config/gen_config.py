import sys
import os

# default config values
data = {'N_SIGS'     : 256,
        'N_ATOMICS ' : 256,
        'N_TL'       : 256,
        'N_AT'       : 256,
        'N_INTERVAL' : 128}

def parse_config(s, data):
    pass

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
