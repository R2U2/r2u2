from asyncio import subprocess
from copy import copy
import csv
import os
from pathlib import Path
from random import randint
from itertools import combinations
from subprocess import run, check_output
from time import perf_counter
from isort import file
import matplotlib.pyplot as plt
from compiler.compiler import benchmark_rewrite_rules #type: ignore


FORMULA_DIR: str = "formulasMLTL"
REWRITE_DIR: str = "rewrite/"
DYN_SET_DIR: str = "dyn-set/"
COUNT_DIR: str = "count/"
CSV_FILENAME: str = "random.csv"
REWRITE_RESULT_DIR: str = "results/rewrite/"
DYN_SET_RESULT_DIR: str = "results/dyn-set/"
COUNT_RESULT_DIR: str = "results/count/"
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
        print(filename.stem)


def generate_dynamic_set_random_benchmark(n: int) -> None:
    """Generates dynamic set specification benchmarks with max size n"""
    prefix: str = generate_file_prefix(n+n*MAX_VARS)

    # generate random mltl formulas
    if not Path("./" + FORMULA_DIR).is_dir():
        run(["perl","generateRandomFormulas_MTLmax.pl"])

    if not Path("./" + DYN_SET_DIR).is_dir():
        os.mkdir(DYN_SET_DIR)
 
    # for each random mltl formula file, add mltl file prefix and write to new file
    spec_set: str = ""
    spec: str = ""
    k: int = 0
    for filename in [f for f in Path("./" + FORMULA_DIR).iterdir()]:
        with open(filename, "r") as f0:
            spec_set = ""
            num_vars = int(filename.stem[5])
            # spec_set += prefix
            for formula in f0.read().splitlines():
                spec = "("
                for i in range(0,n):
                    new_form = copy(formula)
                    for j in reversed(range(0,num_vars)):
                        new_form = new_form.replace(f"(a{j})",f"(a{(i*(num_vars+1))+j+1})")
                    spec += f"(a{(i*(num_vars+1))}->(" + new_form + "))&&"
                spec = spec[:-2]+");\n"
                spec_set += spec
            with open(f"{DYN_SET_DIR}{filename.stem}.mltl","w") as f:
                f.write(prefix+spec_set)
                k += 1
        print(f"{filename.stem}")


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
    if not Path(f"{REWRITE_RESULT_DIR}").is_dir():
        os.mkdir(REWRITE_RESULT_DIR)

    with open(f"./{REWRITE_RESULT_DIR}results.out", "w") as f1:
        for filename in [f for f in Path("./" + REWRITE_DIR).iterdir()]:
            test_name = filename.stem
            prob = float(test_name[1:4])
            len = 0
            if test_name[8] == "M":
                len = int(test_name[7])
            elif test_name[9] == "M":
                len = int(test_name[7:9])
            else:
                len = int(test_name[7:10])
            result = benchmark_rewrite_rules(str(filename),CSV_FILENAME)
            f1.write(f"{prob},{len},{result}\n")
            print(f"{prob},{len},{result}")


def run_dynamic_set_benchmarks() -> None:
    if not Path(f"{DYN_SET_RESULT_DIR}").is_dir():
        os.mkdir(DYN_SET_RESULT_DIR)

    with open(f"./{DYN_SET_RESULT_DIR}results.out", "w") as f1:
        for filename in [f for f in Path("./" + DYN_SET_DIR).iterdir()]:
            test_name = filename.stem
            prob = float(test_name[1:4])
            len = 0
            if test_name[8] == "M":
                len = int(test_name[7])
            elif test_name[9] == "M":
                len = int(test_name[7:9])
            else:
                len = int(test_name[7:10])
            result = benchmark_rewrite_rules(str(filename),CSV_FILENAME)
            f1.write(f"{prob},{len},{result}\n")
            print(f"{prob},{len},{result}")


if __name__ == "__main__":
    # generate_random_csv(1,1000)
    # generate_mltl_rewriting_benchmark()
    # run_mltl_rewriting_benchmarks()
    generate_dynamic_set_random_benchmark(10)
    run_dynamic_set_benchmarks()
    # generate_self_ref_benchmark(2)
    # generate_counting_benchmark(5,2)