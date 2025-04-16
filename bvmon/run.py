import subprocess
import os
import pathlib

def get_time_data(time_output: str) -> tuple[float, int]:
    """Extract time and memory data from the output of a `time` command."""
    time: float = 0
    mem: int = 0
    for line in time_output.splitlines():
        if "Elapsed (wall clock) time " in line:
            time = float(line.split(": ")[1].split(":")[1])
        if "Maximum resident set size" in line:
            mem = int(line.split(": ")[1])
    return (time, mem)


def run_command_n(command: list[str], n: int) -> tuple[float, float, float, int, int, int]:
    """Run a command `n` times and collect time and memory data."""
    time_min: float = 0
    time_max: float = 0
    time_avg: float = 0
    mem_min: int = 0
    mem_max: int = 0
    mem_avg: float = 0

    for _ in range(n):
        proc = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        time, mem = get_time_data(proc.stderr.decode())
        if time_min == 0 or time < time_min:
            time_min = time
        if time_max == 0 or time > time_max:
            time_max = time
        if mem_min == 0 or mem < mem_min:
            mem_min = mem
        if mem_max == 0 or mem > mem_max:
            mem_max = mem
        time_avg += time
        mem_avg += mem

    time_avg /= n
    mem_avg /= n

    return (time_min, time_max, time_avg, mem_min, mem_max, int(mem_avg))


R2U2_C = "../monitors/c/build/r2u2"
R2U2_RUST_DIR = "../monitors/rust/r2u2_cli/"
R2U2_RUST = "../monitors/rust/r2u2_cli/target/release/r2u2_cli"
R2U2_RUST_CONFIG = "../monitors/rust/r2u2_cli/.cargo/config.toml"
C2PO = "../compiler/c2po.py"
HYDRA = "../../hydra/hydra"
HYDRA_FILE = "hydra.mtl"
HYDRA_TRACE = "traces/hydra.log"
TRACE_DIR = "traces"
R2U2_TRACE = "traces/r2u2.csv"
SPEC_FILE = "prec_chain.mltl"
SPEC_BIN = "prec_chain.bin"
TIME = "gtime"
CC = "gcc"
BVMON_FILE = "bvmon.c"
BVMON_BIN = "bvmon"
OUTPUT_DIR = "output"
BVMON_WORD_SIZE = 8

try: 
    os.mkdir(OUTPUT_DIR)
except FileExistsError:
    pass

subprocess.run(["ulimit", "-s", "hard"])

# First we benchmark varying the interval size with a fixed chain length
chain = 5
nsigs = chain + 2
trace_len = 5_000_000

interval_data_r2u2 = {}
interval_data_hydra = {}
interval_data_bvmon_8 = {}
interval_data_bvmon_64 = {}

for ub in [10, 50, 100, 500, 1000, 5000, 10000]:
    print(f"Generating precedence chain formula with ub={ub}")
    command = ["python3", "gen_prec_chain.py", str(ub), str(chain)]
    proc = subprocess.run(command, capture_output=True)
    with open(SPEC_FILE, "wb") as f:
        f.write(proc.stdout)

    density = 2 / ub
    print(f"Generating random trace of len={trace_len}, density={density}")
    command = ["python3", "gen_trace.py", str(trace_len), str(nsigs), str(density), TRACE_DIR]
    proc = subprocess.run(command, capture_output=True)

    print("Compiling spec")
    command = ["python3", C2PO, SPEC_FILE, "-o", SPEC_BIN, "-impl", "rust", "--write-bounds", R2U2_RUST_CONFIG]
    proc = subprocess.run(command, capture_output=True)

    print("Rebuilding r2u2")
    curdir = pathlib.Path(__file__).parent
    os.chdir(R2U2_RUST_DIR)
    command = ["cargo", "clean"]
    proc = subprocess.run(command, capture_output=True)
    command = ["cargo", "build", "--release"]
    proc = subprocess.run(command, capture_output=True)
    os.chdir(curdir)

    print("Checking number verdicts computed by r2u2")
    command = [R2U2_RUST, "run", SPEC_BIN, R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    r2u2_num_verdicts = int(proc.stdout.decode().splitlines()[-1].split(":")[1].split(",")[0])
    print(r2u2_num_verdicts)

    print("Benchmarking r2u2")
    command = [TIME, "-v", R2U2_RUST, "run", SPEC_BIN, R2U2_TRACE]
    (time_min, time_max, time_avg, mem_min, mem_max, mem_avg) = run_command_n(command, 5)
    print(f"\t{time_min}s, {time_max}s, {time_avg:.3f}s, {mem_min}kb, {mem_max}kb, {mem_avg}kb")
    interval_data_r2u2[ub] = (
        r2u2_num_verdicts / time_min,
        r2u2_num_verdicts / time_max,
        r2u2_num_verdicts / time_avg,
        mem_min,
        mem_max,
        mem_avg,
    )
    print(f"\t{r2u2_num_verdicts / time_min}, {r2u2_num_verdicts / time_max}, {r2u2_num_verdicts / time_avg}")

    print("Generating hydra spec")
    command = ["python3", C2PO, "--bnf", "--write-hydra", HYDRA_FILE, "-c", SPEC_FILE]
    subprocess.run(command, capture_output=True)

    print("Checking number verdicts computed by hydra")
    command = [HYDRA, HYDRA_FILE, HYDRA_TRACE]
    proc = subprocess.run(command, capture_output=True)
    hydra_num_verdicts = int(proc.stdout.decode().splitlines()[-1].split(":")[0])
    print(hydra_num_verdicts)

    print("Running hydra")
    command = [TIME, "-v", HYDRA, HYDRA_FILE, HYDRA_TRACE]
    (time_min, time_max, time_avg, mem_min, mem_max, mem_avg) = run_command_n(command, 5)
    print(f"\t{time_min}s, {time_max}s, {time_avg:.3f}s, {mem_min}kb, {mem_max}kb, {mem_avg}kb")
    interval_data_hydra[ub] = (
        hydra_num_verdicts / time_min,
        hydra_num_verdicts / time_max,
        hydra_num_verdicts / time_avg,
        mem_min,
        mem_max,
        mem_avg,
    )
    print(f"\t{hydra_num_verdicts / time_min}, {hydra_num_verdicts / time_max}, {hydra_num_verdicts / time_avg}")
    
    print("Generating bvmon monitor (word_size=8)")
    command = [
        "python3",
        C2PO,
        "--no-rewrite",
        "-c",
        "--extops",
        "--bvmon",
        "--bvmon-nsigs",
        str(nsigs),
        "--bvmon-word-size",
        "8",
        SPEC_FILE
    ]
    proc = subprocess.run(command, capture_output=True)
    with open(BVMON_FILE, "w") as f:
        f.write(proc.stdout.decode())

    print("Compiling bvmon monitor")
    command = [CC, "-O3", "-DOUTPUT", "-o", BVMON_BIN, BVMON_FILE]
    proc = subprocess.run(command, capture_output=True)

    print("Checking number verdicts computed by bvmon (8)")
    command = [f"./{BVMON_BIN}", R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    bvmon_8_num_verdicts = len(proc.stdout.decode().splitlines()) * 8
    print(bvmon_8_num_verdicts)

    print("Running bvmon")
    command = [TIME, "-v", f"./{BVMON_BIN}", R2U2_TRACE]
    (time_min, time_max, time_avg, mem_min, mem_max, mem_avg) = run_command_n(command, 5)
    print(f"\t{time_min}s, {time_max}s, {time_avg:.3f}s, {mem_min}kb, {mem_max}kb, {mem_avg}kb")
    interval_data_bvmon_8[ub] = (
        bvmon_8_num_verdicts / time_min,
        bvmon_8_num_verdicts / time_max,
        bvmon_8_num_verdicts / time_avg,
        mem_min,
        mem_max,
        mem_avg,
    )
    print(f"\t{bvmon_8_num_verdicts / time_min}, {bvmon_8_num_verdicts / time_max}, {bvmon_8_num_verdicts / time_avg}")
    
    print("Generating bvmon monitor (word_size=64)")
    command = [
        "python3",
        C2PO,
        "--no-rewrite",
        "-c",
        "--extops",
        "--bvmon",
        "--bvmon-nsigs",
        str(nsigs),
        "--bvmon-word-size",
        "64",
        SPEC_FILE
    ]
    proc = subprocess.run(command, capture_output=True)
    with open(BVMON_FILE, "w") as f:
        f.write(proc.stdout.decode())

    print("Compiling bvmon monitor")
    command = [CC, "-O3", "-DOUTPUT", "-o", BVMON_BIN, BVMON_FILE]
    proc = subprocess.run(command, capture_output=True)

    print("Checking number verdicts computed by bvmon (64)")
    command = [f"./{BVMON_BIN}", R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    bvmon_64_num_verdicts = len(proc.stdout.decode().splitlines()) * 8
    print(bvmon_64_num_verdicts)

    print("Running bvmon")
    command = [TIME, "-v", f"./{BVMON_BIN}", R2U2_TRACE]
    (time_min, time_max, time_avg, mem_min, mem_max, mem_avg) = run_command_n(command, 5)
    print(f"\t{time_min}s, {time_max}s, {time_avg:.3f}s, {mem_min}kb, {mem_max}kb, {mem_avg}kb")
    interval_data_bvmon_64[ub] = (
        bvmon_64_num_verdicts / time_min,
        bvmon_64_num_verdicts / time_max,
        bvmon_64_num_verdicts / time_avg,
        mem_min,
        mem_max,
        mem_avg,
    )
    print(f"\t{bvmon_64_num_verdicts / time_min}, {bvmon_64_num_verdicts / time_max}, {bvmon_64_num_verdicts / time_avg}")

with open(f"{OUTPUT_DIR}/interval_data_r2u2.csv", "w") as f:
    f.write("ub,time_min,time_max,time_avg,mem_min,mem_max,mem_avg\n")
    for ub, data in interval_data_r2u2.items():
        f.write(f"{ub},{data[0]},{data[1]},{data[2]},{data[3]},{data[4]},{data[5]}\n")

with open(f"{OUTPUT_DIR}/interval_data_hydra.csv", "w") as f:   
    f.write("ub,time_min,time_max,time_avg,mem_min,mem_max,mem_avg\n")
    for ub, data in interval_data_hydra.items():
        f.write(f"{ub},{data[0]},{data[1]},{data[2]},{data[3]},{data[4]},{data[5]}\n")

with open(f"{OUTPUT_DIR}/interval_data_bvmon_8.csv", "w") as f:
    f.write("ub,time_min,time_max,time_avg,mem_min,mem_max,mem_avg\n")
    for ub, data in interval_data_bvmon_8.items():
        f.write(f"{ub},{data[0]},{data[1]},{data[2]},{data[3]},{data[4]},{data[5]}\n")

with open(f"{OUTPUT_DIR}/interval_data_bvmon_64.csv", "w") as f:
    f.write("ub,time_min,time_max,time_avg,mem_min,mem_max,mem_avg\n")
    for ub, data in interval_data_bvmon_64.items():
        f.write(f"{ub},{data[0]},{data[1]},{data[2]},{data[3]},{data[4]},{data[5]}\n")

