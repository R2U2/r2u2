import subprocess
from pathlib import Path

from compiler.c2po.main import compile

TEST_DIR = "test/"
CSE_DIR = f"{TEST_DIR}cse/"
OPERATORS_DIR = f"{TEST_DIR}operators/"
SET_AGG_DIR = f"{TEST_DIR}set_agg/"

class Color:
    PURPLE = "\033[95m"
    BLUE = "\033[94m"
    CYAN = "\033[96m"
    GREEN = "\033[92m"
    YELLOW = "\033[93m"
    RED = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"

def print_header(msg: str) -> None:
    print(Color.BOLD + Color.PURPLE + msg + Color.ENDC)

def print_test_success(filename: str) -> None:
    print(filename + ": " + Color.GREEN + "OK" + Color.ENDC)

def print_test_fail(filename: str) -> None:
    print(filename + ": " + Color.RED + "FAIL" + Color.ENDC)


def test_operators():
    csv_filename = f"{OPERATORS_DIR}operators.csv"

    for file in Path(OPERATORS_DIR).glob("*.mltl"):
        status = compile(str(file), csv_filename, )


def test_set_agg():
    pass


def test_cse():
    pass


if __name__ == "__main__":
    pass