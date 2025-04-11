import random
import os
from struct import Struct as CStruct
import argparse

# Older version of the bvmon trace format where the input is just raw bytes
def bvmon_raw_trace(trace: list[list[bool]], word_size: int) -> bytes:

    def ceildiv(a: int, b: int) -> int:
        return -(a // -b)

    sigil = ""
    if word_size == 8:
        sigil = "B"
    elif word_size == 16:
        sigil = "H"
    elif word_size == 32:
        sigil = "I"
    elif word_size == 64:
        sigil = "Q"

    # trace encoding:
    # bytes 0-7 = trace length (in number of words)
    # bytes 8-8+trace length = values for signal ID
    trace_bin = bytes()
    for prop_trace in trace:
        for i in range(0, len(prop_trace), word_size):
            val = sum(
                [
                    (2**j) if prop_trace[i + (word_size - j - 1)] else 0
                    for j in [
                        k
                        for k in range(0, word_size)
                        if i + (word_size - k - 1) < len(prop_trace)
                    ]
                ]
            )
            trace_bin += CStruct(sigil).pack(val)

    return CStruct("Q").pack(ceildiv(trace_len, word_size)) + trace_bin


def r2u2_trace(trace: list[list[bool]]) -> str: 
    rows = [
        ",".join(["1" if tr[i] else "0" for tr in trace])
        for i in range(len(trace[0]))
    ]
    return "\n".join(rows)


def hydra_trace(trace: list[list[bool]]) -> str: 
    rows = [
        f"@{i} {' '.join([f'a{j}' for j in range(len(trace)) if trace[j][i]])}"
        for i in range(len(trace[0]))
    ]
    return "\n".join(rows)

parser = argparse.ArgumentParser()
parser.add_argument("len", type=int, help="length of generated trace")
parser.add_argument("nsigs", type=int, help="number of signals for eah timestamp")
parser.add_argument("density", type=float, help="relative proportion of trues to falses for each signal")
parser.add_argument("output", help="directory to output traces")
args = parser.parse_args()

trace_len: int = args.len
num_sigs: int = args.nsigs
density: float = args.density 
dir: str = args.output

trace = [random.choices([True, False], weights=[density,1], k=trace_len) for _ in range(num_sigs)]

r2u2_tr = r2u2_trace(trace)
hydra_tr = hydra_trace(trace)
# bvmon_tr = bvmon_raw_trace(trace, word_size)

try:
    os.mkdir(dir)
except FileExistsError:
    pass

with open(f"{dir}/r2u2.csv", "w") as f:
    f.write(r2u2_tr)
with open(f"{dir}/hydra.log", "w") as f:
    f.write(hydra_tr)
