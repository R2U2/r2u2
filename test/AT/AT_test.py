import csv
import random
import os
import sys
import subprocess

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__CDir__         = __AbsolutePath__+'../../R2U2_SW/R2U2_C/'
__PrepDir__      = __AbsolutePath__+'../../tools/'

rows = 50

# col0: bool
# col1: int
# col2: double
# col3: abs_diff_angle
# etc.
filters = ['bool','int','double','abs_diff_angle','rate','movavg']
avail_cond = ['<','<=','>','>=']
cond = ['','','','','','']
const = [0,0,0,0,0,0]
arg = [0,0,0,0,0,0]
movavg_buffer = []
rate_tmp = 0.0

###############################################################################
# Generate values
###############################################################################

def boolean():
    return random.randrange(2)

def integer():
    return random.randrange(-10000,10000)

def double():
    return random.uniform(-10000,10000)

def angle():
    return random.randrange(-360, 360)

def gen_values():
    global filters
    values = []

    for filt in filters:
        if filt == 'bool':
            values.append(boolean())
        elif filt == 'int':
            values.append(integer())
        elif filt == 'double':
            values.append(double())
        elif filt == 'abs_diff_angle':
            values.append(angle())
        elif filt == 'rate':
            values.append(double())
        elif filt == 'movavg':
            values.append(integer())

    return values

def write_values(filename):
    global rows
    with open(filename, 'w', newline='') as f:
        writer = csv.writer(f)
        for i in range(rows):
            writer.writerow(gen_values())

###############################################################################
# Generate AT formulas
###############################################################################

def gen_at_formula(filt):
    if filt == 'bool':
        cond[0] = random.choice(['==','!='])
        const[0] = boolean()
        return 'bool(0) ' + cond[0] + ' ' + str(const[0])
    elif filt == 'int':
        cond[1] = random.choice(avail_cond)
        const[1] = integer()
        return 'int(1) ' + cond[1] + ' ' + str(const[1])
    elif filt == 'double':
        cond[2] = random.choice(avail_cond)
        const[2] = integer()
        return 'double(2) ' + cond[2] + ' ' + str(const[2])
    elif filt == 'abs_diff_angle':
        cond[3] = random.choice(avail_cond)
        const[3] = angle()
        arg[3] = angle()
        return 'abs_diff_angle(3,' + str(arg[3]) + ') ' + cond[3] + \
            ' ' + str(const[3])
    elif filt == 'rate':
        cond[4] = random.choice(avail_cond)
        const[4] = integer()
        return 'rate(4) ' + cond[4] + ' ' + str(const[4])
    elif filt == 'movavg':
        cond[5] = random.choice(avail_cond)
        const[5] = integer()
        arg[5] = integer()
        return 'movavg(5,' + str(arg[5]) + ') ' + cond[5] + \
            ' ' + str(const[5])

    return ''

def write_formulas(filename):
    s = ''
    for i in range(len(filters)):
        s += 'a' + str(i) + ';\n'
    for i in range(len(filters)):
        s += 'a' + str(i) + ' := ' + gen_at_formula(filters[i]) + ';\n'
    with open(filename, 'w') as f:
        f.write(s)

###############################################################################
# Check AT outputs
###############################################################################

def read_values(filename):
    values = []
    with open(filename, newline='') as f:
        reader = csv.reader(f)
        for row in reader:
            values.append(row)
    return values

def compare(sig, bool, constant, comp):
    if comp == '==':
        return (sig == constant) == bool
    elif comp == '!=':
        return (sig != constant) == bool
    elif comp == '<':
        return (sig < constant) == bool
    elif comp == '<=':
        return (sig <= constant) == bool
    elif comp == '>':
        return (sig > constant) == bool
    elif comp == '>=':
        return (sig >= constant) == bool
    return False

def check_bool(log, sig, bool):
    sig = int(sig)
    bool = int(bool)

    result = compare(sig, bool, const[0], cond[0])

    s = 'BOOL: (' + str(sig) + ' ' + cond[0] + ' ' + str(const[0]) + ') == ' + \
        str(bool) + ' -> ' + str(result) + '\n'
    log.write(s)

    return result

def check_int(log, sig, bool):
    sig = int(sig)
    bool = int(bool)

    result = compare(sig, bool, const[1], cond[1])

    s = 'INT: (' + str(sig) + ' ' + cond[1] + ' ' + str(const[1]) + ') == ' + \
        str(bool) + ' -> ' + str(result) + '\n'
    log.write(s)

    return result

def check_double(log, sig, bool):
    sig = float(sig)
    bool = int(bool)

    result = compare(sig, bool, const[2], cond[2])

    s = 'DOUBLE: (' + str(sig) + ' ' + cond[2] + ' ' + str(const[2]) + ') == ' + \
        str(bool) + ' -> ' + str(result) + '\n'
    log.write(s)

    return result

def check_abs_diff_angle(log, sig, bool):
    sig = float(sig)
    bool = int(bool)

    norm_angle = (sig - arg[3]) % 360
    abs_diff_angle = min(norm_angle, 360 - norm_angle)

    result = compare(abs_diff_angle, bool, const[3], cond[3])

    s = 'ABS_DIFF_ANGLE: norm = ' + str(sig) + ' - ' + str(arg[3]) + \
        ' % 360 = ' + str(norm_angle) + '\n'
    s += 'ABS_DIFF_ANGLE: diff_angle = min(' + str(norm_angle) + ', 360 - ' \
        + str(norm_angle) + ') = ' + str(abs_diff_angle) + '\n'
    s = 'ABS_DIFF_ANGLE: (' + str(abs_diff_angle) + ' ' + cond[3] + ' ' + \
        str(const[3]) + ') == ' + str(bool) + ' -> ' + str(result) + '\n'
    log.write(s)

    return result

def check_rate(log, sig, bool):
    global rate_tmp
    sig = float(sig)
    bool = int(bool)

    diff = sig - rate_tmp

    s = 'RATE: diff = ' + str(sig) + ' - ' + str(rate_tmp) + ' = ' + \
        str(diff) + '\n'

    rate_tmp = sig

    result = compare(diff, bool, const[4], cond[4])

    s += 'RATE: (' + str(diff) + ' ' + cond[4] + ' ' + str(const[4]) + \
        ') == ' + str(bool) + ' -> ' + str(result) + '\n'
    log.write(s)

    return result

def check_movavg(log, sig, bool):
    global movavg_buffer
    sig = float(sig)
    bool = int(bool)

    if len(movavg_buffer) == arg[5]:
        movavg_buffer.pop(0)
    movavg_buffer.append(sig)
    avg = sum(movavg_buffer) / len(movavg_buffer)

    result = compare(avg, bool, const[5], cond[5])

    s = 'MOVAVG: buffer = ' + str(movavg_buffer) + '\n'
    s += 'MOVAVG: avg = ' + str(sum(movavg_buffer)) + ' / ' + \
        str(len(movavg_buffer)) + ' = ' + str(avg) + '\n'
    s += 'MOAVG: (' + str(avg) + ' ' + cond[5] + ' ' + str(const[5]) + \
        ') == ' + str(bool) + ' -> ' + str(result) + '\n'
    log.write(s)

    return result

def compare_output(sig_filename, bool_filename):
    sigs = read_values(sig_filename)
    bools = read_values(bool_filename)

    with open('log/'+sys.argv[4], 'w') as log:
        for row in range(len(sigs)):
            log.write('--- Time step ' + str(row) + ' ---\n')
            if not check_bool(log, sigs[row][0], bools[row][0]):
                print('BOOL: Failed at time step ' + str(row))
            if not check_int(log, sigs[row][1], bools[row][1]):
                print('INT: Failed at time step ' + str(row))
            if not check_double(log, sigs[row][2], bools[row][2]):
                print('DOUBLE: Failed at time step ' + str(row))
            if not check_abs_diff_angle(log, sigs[row][3], bools[row][3]):
                print('ABS_DIFF_ANGLE: Failed at time step ' + str(row))
            if not check_rate(log, sigs[row][4], bools[row][4]):
                print('RATE: Failed at time step ' + str(row))
            if not check_movavg(log, sigs[row][5], bools[row][5]):
                print('MOVAVG: Failed at time step ' + str(row))
            log.write('\n')

if __name__ == '__main__':
    print('Running AT checker test')

    print('Generating test signal values at ' + sys.argv[1])
    write_values(sys.argv[1])

    print('Generating test mltl formula file at ' + sys.argv[2])
    write_formulas(sys.argv[2])

    print('Running r2u2prep.py using ' + sys.argv[2] + ' and logging output at log/prep.log')
    prep_log = open('log/prep.log', 'w')
    subprocess.run(['python3', __PrepDir__+'r2u2prep.py', \
        __AbsolutePath__+sys.argv[2]], stdout=prep_log)

    print('Running r2u2 and piping boolean output to ' + sys.argv[3] + ' and logging debug output at log/r2u2_debug.log')
    r2u2_debug_log = open('log/r2u2_debug.log', 'w')
    bool_log = open(sys.argv[3], 'w')
    subprocess.run([__CDir__+'bin/r2u2', __PrepDir__+'binary_files/',\
        __AbsolutePath__+sys.argv[1]], stderr=r2u2_debug_log, stdout=bool_log)

    print('Checking boolean output and logging at log/' + sys.argv[4])
    compare_output(sys.argv[1], sys.argv[3])
