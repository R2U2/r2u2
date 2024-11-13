import csv
from random import randint
from typing import Callable, Tuple
from time import perf_counter
from pathlib import Path

import sys
sys.path.append(str((Path(__file__).parent / ".." / ".." ).absolute()))

from compiler.c2po.log import logger # noqa: E402
from compiler.c2po.cpt import Node # noqa: E402
from compiler.c2po.main import * # noqa: E402

"""
Process for running benchmark:
1. Generate random MLTL formulas (with params P,L,N,M)
2. Generate random csv file
3. For each random MLTL file, 
  a. Generate file prefix, use to create well-type C2PO file
  b. Run benchmark over C2PO file
"""

# ------------------------------------------------------------------------------
# File/Formula generation
# ------------------------------------------------------------------------------

def generate_file_prefix(n: int) -> str:
    """Generate file prefix with 'n' variables of type bool."""
    s: str = "INPUT\n"
    for i in range(0, n):
        s += "a" + str(i) + ","
    s = s[:-1]
    s += ": bool;\nSPEC\n"
    return s


def generate_random_csv(filename: str, r: int, n: int) :
    """Generate csv file with 'r' rows of 'n' Boolean variables"""
    if not Path(filename).exists():
        with open(filename, "w") as f:
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


# ------------------------------------------------------------------------------
# Benchmarking
# ------------------------------------------------------------------------------

def benchmark(input: str, func: Callable[[Node],None]) -> Tuple[float,int,int]:
    """Runs 'func' as a benchmark, returns a tuple with (time,pre,post) where 
    'time' is the time taken to run 'func' and 'pre'/'post' are the memory of 
    a before and after running func respectively"""
    programs = parse(input)

    if len(programs) < 1:
        log.error(' Failed parsing.')
        return (0,0,0)
    elif len(programs) > 1:
        log.error('Only one program allowed in benchmark')
        return (0,0,0)

    a: Node = programs[0]

    pre: int = compute_scq_size(a)
    t1: float = perf_counter()
    func(a)
    t2: float = perf_counter()
    post: int = compute_scq_size(a)

    return (t2-t1, pre, post)


def benchmark_list(
    input: str, 
    funcs: list[Callable[[Node],None]],
) -> list[tuple[float,int,int]]:
    """Benchmarks each function in 'funcs'"""  
    programs = parse(input)

    if len(programs) < 1:
        log.error(' Failed parsing.')
        return []
    elif len(programs) > 1:
        log.error('Only one program allowed in benchmark')
        return []

    a: Node = programs[0]
    results: list[tuple[float,int,int]] = []

    pre: int = compute_scq_size(a)
    t1: float = perf_counter()

    for func in funcs:
        func(a)
        t2: float = perf_counter()
        post: int = compute_scq_size(a)
        results.append((t2-t1,pre,post))
        pre = post

    return results



