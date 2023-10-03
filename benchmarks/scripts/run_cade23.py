from itertools import combinations
import os
from copy import copy
from subprocess import run
from pathlib import Path
from benchmark import generate_file_prefix, benchmark
from c2po.main import optimize_rewrite_rules

DIR = "../cade23/"
RESULTS_DIR = DIR+"results/"
DYN_SET_FORMULA_DIR = DIR+"dyn-set/"
DYN_SET_RESULTS_DIR = RESULTS_DIR+"dyn-set/"
COUNT_RESULTS_DIR = RESULTS_DIR+"count/"


def run_dynamic_set_benchmark(sizes: list[int]) :
    formula = "(G[0,100](a0) && G[0,100](a1))"

    with open(f"{DYN_SET_RESULTS_DIR}select.out", "w") as f:
        results: str = ""
        for n in sizes:
            spec: str = generate_file_prefix(n*3)
            spec += "("
            for i in range(0,n):
                new_form = copy(formula)
                new_form = new_form.replace(f"(a1)",f"(a{(i*3)+2})")
                new_form = new_form.replace(f"(a0)",f"(a{(i*3)+1})")
                spec += f"(a{(i*3)}->(" + new_form + "))&&"
            spec = spec[:-2]+");\n"

            results += f"{n}, {str(benchmark(spec, optimize_rewrite_rules))[1:-1]}\n"

        f.write(results)


def run_counting_benchmark(sizes: list[int], chooses: list[int]) :
    formula = "(G[0,100](a0) && G[0,100](a1))"

    with open(f"{COUNT_RESULTS_DIR}select.out", "w") as f:
        results: str = ""
        for n in sizes:
            for k in [i for i in chooses if i < n]:
                spec: str = generate_file_prefix(n*3)
                spec += "("
                for i in range(0,k+1):
                    for combo in combinations(range(0,n),n-i):
                        spec += "("
                        for j in range(0,n):
                            new_form = formula.replace(f"(a1)",f"(a{(j*3)+2})")
                            new_form = new_form.replace(f"(a0)",f"(a{(j*3)+1})")
                            spec += f"(!(a{j*3}&&{new_form}))&&" if j in combo else f"(a{j*3}&&{new_form})&&"
                        spec = spec[:-2] + ")||"
                spec = spec[:-2]+");\n"

                results += f"{n}, {k}, {str(benchmark(spec, optimize_rewrite_rules))[1:-1]}\n"

        f.write(results)


def main():
    if not Path(DIR).is_dir():
        os.mkdir(DIR)

    # if not Path(FORMULA_DIR).is_dir():
    #     os.mkdir(FORMULA_DIR)
    #     run(["perl","random_mltl.pl"])

    if not Path(RESULTS_DIR).is_dir():
        os.mkdir(RESULTS_DIR)

    if not Path(DYN_SET_RESULTS_DIR).is_dir():
        os.mkdir(DYN_SET_RESULTS_DIR)

    if not Path(COUNT_RESULTS_DIR).is_dir():
        os.mkdir(COUNT_RESULTS_DIR)

    run_dynamic_set_benchmark([2**i for i in range(1,14)])
    run_counting_benchmark([n for n in range(1,12)], [k for k in range(1,8)])


if __name__ == "__main__":
    main()