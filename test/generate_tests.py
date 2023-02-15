import csv
import os
from pathlib import Path
from random import randint
from subprocess import run

FORMULA_DIR: str = 'formulasMLTL/'
MLTL_DIR: str = 'tmp/'
CSV_FILENAME: str = 'random.csv'
NUM_VARS: int = 5
NUM_ROWS: int = 100

def generate_file_prefix(n: int) -> str:
    """Generate file prefix with n variables of type bool."""
    s: str = 'INPUT\n'
    for i in range(0, n):
        s += 'a' + str(i) + ','
    s = s[:-1]
    s += ': bool;\nSPEC\n'
    return s

def generate_random_mltl(prefix: str) -> None:
    """For each file in FORMULA_DIR, generate an MLTL file in MLTL_DIR using prefix."""

    # generate random mltl formulas
    if not Path('./' + FORMULA_DIR).is_dir():
        run(['perl','generateRandomFormulas_MTLmax.pl'])

    if not Path('./' + MLTL_DIR).is_dir():
        os.mkdir(MLTL_DIR)

    # for each random mltl formula file, add mltl file prefix and write to new file
    for filename in Path('./' + FORMULA_DIR).iterdir():
        with open(filename, 'r') as f0:
            with open('./' + MLTL_DIR + str(filename.name)[:-4] + '.mltl', 'w') as f1:
                f1.write(prefix + f0.read())

def generate_random_csv(r: int, n: int) -> None:
    """Generate csv file with r rows of n Boolean variables"""
    if not Path(CSV_FILENAME).exists():
        with open(CSV_FILENAME, 'w') as f:
            csvwriter = csv.writer(f)

            l: list[str] = []
            for i in range(0,n):
                l.append('a'+str(i))
            csvwriter.writerow(l)

            for i in range(0,r):
                l = []
                for j in range(0,n):
                    l.append(str(randint(0,1)))
                csvwriter.writerow(l)

if __name__ == '__main__':
    generate_random_mltl(generate_file_prefix(NUM_VARS))
    generate_random_csv(NUM_ROWS,NUM_VARS)