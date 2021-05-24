import csv
import random
import os
import sys
import subprocess

__AbsolutePath__ = os.path.dirname(os.path.abspath(__file__))+'/'
__CDir__         = __AbsolutePath__+'../../R2U2_C/'
__PrepDir__      = __AbsolutePath__+'../../tools/'


# col0: bool
# col1: int
# col2: float
# col3: abs_diff_angle
# etc.
filters = ['bool','int','float','abs_diff_angle','rate','movavg']
avail_cond = ['<','<=','>','>=']
cond = ['','','','','','']
const = [0,0,0,0,0,0]
arg = [0,0,0,0,0,0]
movavg_buffer = []
rate_tmp = 0.0

###############################################################################
# Generate values
###############################################################################

def gen_boolean():
    return random.randrange(2)

def gen_integer():
    return random.randrange(-10000,10000)

def gen_float():
    return random.uniform(-10000,10000)

def gen_angle():
    return random.randrange(-360, 360)

def gen_values():
    global filters
    values = []

    for filt in filters:
        if filt == 'bool':
            values.append(gen_boolean())
        elif filt == 'int':
            values.append(gen_integer())
        elif filt == 'float':
            values.append(gen_float())
        elif filt == 'abs_diff_angle':
            values.append(gen_angle())
        elif filt == 'rate':
            values.append(gen_float())
        elif filt == 'movavg':
            values.append(gen_integer())

    return values

def write_values(num_rows, filename):
    with open(filename, 'w', newline='') as f:
        writer = csv.writer(f)
        for i in range(num_rows):
            writer.writerow(gen_values())

###############################################################################
# Generate AT formulas
###############################################################################

def gen_at_formula(filt):
    if filt == 'bool':
        cond[0] = random.choice(['==','!='])
        const[0] = gen_boolean()
        return 'bool(s0) ' + cond[0] + ' ' + str(const[0])
    elif filt == 'int':
        cond[1] = random.choice(avail_cond)
        const[1] = gen_integer()
        return 'int(s1) ' + cond[1] + ' ' + str(const[1])
    elif filt == 'float':
        cond[2] = random.choice(avail_cond)
        const[2] = gen_integer()
        return 'float(s2) ' + cond[2] + ' ' + str(const[2])
    elif filt == 'abs_diff_angle':
        cond[3] = random.choice(avail_cond)
        const[3] = gen_angle()
        arg[3] = gen_angle()
        return 'abs_diff_angle(s3,' + str(arg[3]) + ') ' + cond[3] + \
            ' ' + str(const[3])
    elif filt == 'rate':
        cond[4] = random.choice(avail_cond)
        const[4] = gen_integer()
        return 'rate(s4) ' + cond[4] + ' ' + str(const[4])
    elif filt == 'movavg':
        cond[5] = random.choice(avail_cond)
        const[5] = gen_integer()
        arg[5] = gen_integer()
        return 'movavg(s5,' + str(arg[5]) + ') ' + cond[5] + \
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

def check_float(log, sig, bool):
    sig = float(sig)
    bool = int(bool)

    result = compare(sig, bool, const[2], cond[2])

    s = 'float: (' + str(sig) + ' ' + cond[2] + ' ' + str(const[2]) + ') == ' + \
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

def compare_output(testlog_filename, sig_filename, bool_filename):
    sigs = read_values(sig_filename)
    bools = read_values(bool_filename)

    with open('log/' + testlog_filename, 'w') as log:
        for row in range(len(sigs)):
            log.write('--- Time step ' + str(row) + ' ---\n')
            if not check_bool(log, sigs[row][0], bools[row][0]):
                print('BOOL: Failed at time step ' + str(row))
            if not check_int(log, sigs[row][1], bools[row][1]):
                print('INT: Failed at time step ' + str(row))
            if not check_float(log, sigs[row][2], bools[row][2]):
                print('float: Failed at time step ' + str(row))
            if not check_abs_diff_angle(log, sigs[row][3], bools[row][3]):
                print('ABS_DIFF_ANGLE: Failed at time step ' + str(row))
            if not check_rate(log, sigs[row][4], bools[row][4]):
                print('RATE: Failed at time step ' + str(row))
            if not check_movavg(log, sigs[row][5], bools[row][5]):
                print('MOVAVG: Failed at time step ' + str(row) )
            log.write('\n')

if __name__ == '__main__':
    print('Running AT checker test')

    if not len(sys.argv) == 2:
        sys.exit('Usage: python AT_test.py num_rows')

    try:
        num_rows = int(sys.argv[1])
    except TypeError:
        print('num_rows must be integer')
        sys.exit('Usage: python AT_test.py num_rows')

    if not os.path.exists('log'):
        os.makedirs('log')
    if not os.path.exists('data'):
        os.makedirs('data')

    sig_filename = 'signals.csv'
    mltl_filename = 'formula.mltl'
    r2u2prep_filename = 'r2u2prep.log'
    r2u2debug_filename = 'r2u2debug.log'
    bool_filename = 'ATout.csv'
    testlog_filename = 'AT_test.log'

    print('Generating test signal values at data/' + sig_filename)
    write_values(num_rows, 'data/' + sig_filename)

    print('Generating test mltl formula file at data/' + mltl_filename)
    write_formulas('data/' + mltl_filename)

    print('Running r2u2prep.py using ' + mltl_filename + \
        ' and logging output at log/' + r2u2prep_filename)
    prep_log = open('log/' + r2u2prep_filename, 'w')
    subprocess.run(['python3', __PrepDir__+'r2u2prep.py', \
        'data/' + mltl_filename], stdout = prep_log)

    print('Running r2u2 and piping boolean output to data/' + bool_filename \
        + ' and logging debug output at log/' + r2u2debug_filename)
    r2u2_debug_log = open('log/' + r2u2debug_filename, 'w')
    bool_log = open('data/' + bool_filename, 'w')
    subprocess.run([__CDir__+'bin/r2u2', __PrepDir__+'binary_files/',\
        'data/' + sig_filename], stderr = r2u2_debug_log, stdout = bool_log)

    print('Checking boolean output and logging at log/' + testlog_filename)
    compare_output(testlog_filename, 'data/' + sig_filename, \
        'data/' + bool_filename)
