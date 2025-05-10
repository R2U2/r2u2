import random
import os
import argparse

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

try:
    os.mkdir(dir)
except FileExistsError:
    pass

with open(f"{dir}/r2u2.csv", "w") as f:
    f.write(r2u2_tr)
with open(f"{dir}/hydra.log", "w") as f:
    f.write(hydra_tr)
