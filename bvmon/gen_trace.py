import random
import sys
from struct import Struct as CStruct

def bvmon_trace(trace: list[list[bool]], word_size: int) -> bytes:

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
            val = 0
            for j in [k for k in range(0, word_size) if i + (word_size - k - 1) < len(prop_trace)]:
                val += (2 ** j) if prop_trace[i + (word_size - j - 1)] else 0
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


if __name__ == "__main__":
    trace_len = int(sys.argv[1])
    num_sigs = int(sys.argv[2])
    word_size = int(sys.argv[3])
    # assert trace_len % word_size == 0

    trace = [[random.choice([True, False]) for _ in range(trace_len)] for _ in range(num_sigs)]

    r2u2_tr = r2u2_trace(trace)
    hydra_tr = hydra_trace(trace)
    bvmon_tr = bvmon_trace(trace, word_size)

    with open("trace.r2u2.log", "w") as f:
        f.write(r2u2_tr)
    with open("trace.hydra.log", "w") as f:
        f.write(hydra_tr)
    with open("trace.bvmon.log", "wb") as f:
        f.write(bvmon_tr)
