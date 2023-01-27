import logging
import os
import re
import subprocess

TEST_DIR = 'test/'
INPUT_FILE = TEST_DIR+'input.csv'
LOG_FILE = 'test.log'

SUCCESS_CODE = 0

class Color:
    PURPLE = '\033[95m'
    BLUE = '\033[94m'
    CYAN = '\033[96m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    RED = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

def print_header(msg: str) -> None:
    print(Color.BOLD + Color.PURPLE + msg + Color.ENDC)

def print_test_success(filename: str) -> None:
    print(filename + ': ' + Color.GREEN + 'OK' + Color.ENDC)

def print_test_fail(filename: str) -> None:
    print(filename + ': ' + Color.RED + 'FAIL' + Color.ENDC)

def run_with_booleanizer(filename: str) -> subprocess.CompletedProcess:
    return subprocess.run(['python','r2u2prep.py','--booleanizer',filename,INPUT_FILE],capture_output=True,text=True)

def run_without_booleanizer(filename: str) -> subprocess.CompletedProcess:
    return subprocess.run(['python','r2u2prep.py',filename,INPUT_FILE],capture_output=True,text=True)

def test_files(files: list[str], bz: bool, ret_code: int) -> bool:
    status = True

    for filename in files:
        if bz:
            ret = run_with_booleanizer(filename)
        else:
            ret = run_without_booleanizer(filename)

        if ret.returncode != ret_code:
            status = False
            print_test_fail(filename)
            with open(LOG_FILE,'w+') as log_file:
                log_file.write('----\n')
                log_file.write(filename)
                log_file.write(ret.stderr)
                log_file.write('----\n')
        else:
            print_test_success(filename)

    return status


def test_operators() -> bool:
    status = True
    dir = TEST_DIR+'operators/'
    bz_files = ['arithmetic.mltl','bitwise.mltl','relational.mltl']
    tl_files = ['logic.mltl','temporal.mltl']

    print_header('Testing operators')

    status = test_files([dir+f for f in bz_files], True, SUCCESS_CODE)
    status = test_files([dir+f for f in tl_files], False, SUCCESS_CODE) and status

    return status


def test_set_aggregation() -> bool:
    status = True
    dir = TEST_DIR+'set_agg/'
    bz_files = ['basic.mltl','struct_set_combo.mltl','struct_set.mltl', 'var_set.mltl']

    print_header('Testing set aggregation operators')

    status = test_files([dir+f for f in bz_files], True, SUCCESS_CODE)

    return status

if __name__ == '__main__':
    status = test_operators()
    status = test_set_aggregation() and status

    if not status:
        print('See ' + LOG_FILE)
