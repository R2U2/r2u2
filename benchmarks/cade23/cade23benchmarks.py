from asyncio import subprocess
import csv
import os
from pathlib import Path
from random import randint
from itertools import combinations
from subprocess import run, check_output
import matplotlib.pyplot as plt


FORMULA_DIR: str = "formulasMLTL"
REWRITE_DIR: str = "rewrites/"
SELF_REF_DIR: str = "self_ref/"
COUNT_DIR: str = "count/"
CSV_FILENAME: str = "random.csv"
RESULT_DIR: str = "results/"
R2U2_PREP: str = "../../tools/r2u2prep.py"

NUM_VARS: int = 5
NUM_ROWS: int = 100
MAX_VARS: int = 5


def generate_file_prefix(n: int) -> str:
    """Generate file prefix with n variables of type bool."""
    s: str = "INPUT\n"
    for i in range(0, n):
        s += "a" + str(i) + ","
    s = s[:-1]
    s += ": bool;\nSPEC\n"
    return s


def generate_random_csv(r: int, n: int) -> None:
    """Generate csv file with r rows of n Boolean variables"""
    if not Path(CSV_FILENAME).exists():
        with open(CSV_FILENAME, "w") as f:
            csvwriter = csv.writer(f)

            l: list[str] = []
            for i in range(0,n):
                l.append("a"+str(i))
            csvwriter.writerow(l)

            for i in range(0,r):
                l = []
                for j in range(0,n):
                    l.append(str(randint(0,1)))
                csvwriter.writerow(l)


def generate_mltl_rewriting_benchmark() -> None:
    prefix: str = generate_file_prefix(MAX_VARS)

    # generate random mltl formulas
    if not Path("./" + FORMULA_DIR).is_dir():
        run(["perl","generateRandomFormulas_MTLmax.pl"])

    if not Path(f"./{REWRITE_DIR}").is_dir():
        os.mkdir(REWRITE_DIR)

    for filename in [f for f in Path("./" + FORMULA_DIR).iterdir()]:
        spec = ""
        with open(filename, "r") as f0:
            for formula in f0.read().splitlines():
                spec += formula+";\n"
            spec = spec[:-2]
            with open(f"{REWRITE_DIR}{filename.stem}.mltl", "w") as f1:
                f1.write(prefix+spec+";")


def generate_self_ref_benchmark(n: int) -> None:
    if not Path("./" + SELF_REF_DIR).is_dir():
        os.mkdir(SELF_REF_DIR)

    # each spec requires two vars
    prefix: str = generate_file_prefix(n*2)

    # if a request is "received", it will be "granted" within 10 time steps
    spec: str = ""
    for i in range(0,n*2,2):
        spec += f"(!a{i}||F[1,10](a{i+1}))&&"
    spec = spec[:-2]+";"

    print(prefix+spec)


def generate_self_ref_benchmark_random(n: int, p: int) -> None:
    """Generates a self-referential specification using n entities and p properties of each"""
    # each spec requires two vars
    prefix: str = generate_file_prefix(n*p)

    # generate random mltl formulas
    if not Path("./" + FORMULA_DIR).is_dir():
        run(["perl","generateRandomFormulas_MTLmax.pl"])

    if not Path("./" + SELF_REF_DIR).is_dir():
        os.mkdir(SELF_REF_DIR)

    # for each random mltl formula file, add mltl file prefix and write to new file
    spec_set: str = ""
    spec: str = ""
    k: int = 0
    for filename in [f for f in Path("./" + FORMULA_DIR).iterdir() if str(f).find('N'+str(p)) != -1]:
        with open(filename, "r") as f0:
            for formula in f0.read().splitlines():
                spec = "("
                for i in range(0,n):
                    for j in range(0,p):
                        spec += "(" + formula.replace(f"a{j}",f"a{(i*n)+j}") + ")&&"
                spec = spec[:-2]+");"
                with open(f"{SELF_REF_DIR}self_ref{k}.mltl","w") as f:
                    f.write(prefix+spec)
                    k += 1


def generate_counting_benchmark(size: int, n: int) -> None:
    """Generates a counting specification of the form: 'no more than n out of size atoms are true'"""
    assert n <= size

    if not Path("./" + COUNT_DIR).is_dir():
        os.mkdir(COUNT_DIR)

    # each spec requires two vars
    prefix: str = generate_file_prefix(size)

    # no more than "n" tasks are "in progress" on the scheduler at once
    # (assume tasks have states "in queue", "in progress", "paused", "completed", etc.)
    basic_spec: str = "!("
    for i in range(n,size):
        for combo in combinations(range(0,size),size-i):
            basic_spec += "("
            for j in range(0,size):
                basic_spec += f"!a{j}&&" if j in combo else f"a{j}&&"
            basic_spec = basic_spec[:-2] + ")||"
    basic_spec += "("
    for j in range(0,size):
        basic_spec += f"a{j}&&"
    basic_spec = basic_spec[:-2]+"));"

    print(prefix+basic_spec)


def run_mltl_rewriting_benchmarks() -> None:
    if not Path(f"{RESULT_DIR}").is_dir():
        os.mkdir(RESULT_DIR)

    for filename in [f for f in Path("./" + REWRITE_DIR).iterdir()]:
        result = run(["python",R2U2_PREP,filename,CSV_FILENAME], stdout=subprocess.PIPE)
        with open(f"./{RESULT_DIR}{filename.stem}.out", "w") as f1:
            f1.write(result.stdout.decode("utf-8"))
            print(f"wrote to {RESULT_DIR}{filename.stem}.out")


if __name__ == "__main__":
    # generate_mltl_rewriting_benchmark()
    run_mltl_rewriting_benchmarks()
    # generate_self_ref_benchmark_random(2,3)
    # generate_self_ref_benchmark(2)
    # generate_counting_benchmark(10,2)