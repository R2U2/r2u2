import subprocess
import os
import pathlib
import argparse
import sys

R2U2_RUST_DIR = "../monitors/rust/r2u2_cli/"
R2U2_RUST = "../monitors/rust/r2u2_cli/target/release/r2u2_cli"
R2U2_RUST_CONFIG = "../monitors/rust/r2u2_cli/.cargo/config.toml"
R2U2_C_DIR = "../monitors/c/"
R2U2_C = "../monitors/c/build/r2u2"
R2U2_C_BOUNDS = "../monitors/c/src/internals/bounds.h"
C2PO = "../compiler/c2po.py"
HYDRA = "../../hydra/hydra"
HYDRA_FILE = "hydra.mtl"
HYDRA_TRACE = "traces/hydra.log"
HYDRA_OUTPUT = "traces/hydra_output.log"
R2U2_OUTPUT = "traces/r2u2_output.log"
BVMON_OUTPUT = "traces/bvmon_output.log"
TRACE_DIR = "traces"
R2U2_TRACE = "traces/r2u2.csv"
SPEC_BIN = "spec.bin"
SPEC_FILE = "spec.mltl"
TIME = "gtime" if sys.platform == "darwin" else "/usr/bin/time"
CC = "gcc"
BVMON_FILE = "bvmon.c"
BVMON_BIN = "bvmon"
OUTPUT_DIR = "output"
BVMON_DEFAULT_WORD_SIZE = 8

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


def run_command_n(command: list[str], n: int) -> tuple[float, float]:
    """Run a command `n` times and collect average time and memory data."""
    time_avg: float = 0
    mem_avg: float = 0

    for _ in range(n):
        proc = subprocess.run(command, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
        time, mem = get_time_data(proc.stderr.decode())
        time_avg += time
        mem_avg += mem

    time_avg /= n
    mem_avg /= n

    return (time_avg, mem_avg)


def recompile_r2u2_c(spec: str) -> None:
    print("Compiling spec (C)")
    command = ["python3", C2PO, spec, "-o", "spec.bin", "--write-bounds", R2U2_C_BOUNDS]
    subprocess.run(command, capture_output=True)

    print("Rebuilding r2u2 (C)")
    curdir = pathlib.Path(__file__).parent
    os.chdir(R2U2_C_DIR)
    command = ["make", "clean"]
    subprocess.run(command, capture_output=True)
    command = ["make"]
    subprocess.run(command, capture_output=True)
    os.chdir(curdir)


def benchmark_r2u2_c(n: int) -> tuple[float, float]:
    print("Checking number verdicts computed by r2u2 (C)")
    command = [R2U2_C, SPEC_BIN, R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    num_verdicts = int(proc.stdout.decode().splitlines()[-1].split(":")[1].split(",")[0])

    print("Benchmarking r2u2 (C)")
    command = [TIME, "-v", R2U2_C, SPEC_BIN, R2U2_TRACE]
    time_avg, mem_avg = run_command_n(command, n)
    throughput_avg = num_verdicts / time_avg
    return (throughput_avg, mem_avg)


def recompile_r2u2_rust(spec: str) -> None:
    print("Compiling spec (Rust)")
    command = ["python3", C2PO, spec, "-o", "spec.bin", "--impl", "rust", "--write-bounds", R2U2_RUST_CONFIG]
    subprocess.run(command, capture_output=True)

    print("Rebuilding r2u2 (Rust)")
    curdir = pathlib.Path(__file__).parent
    os.chdir(R2U2_RUST_DIR)
    command = ["cargo", "clean"]
    subprocess.run(command, capture_output=True)
    command = ["cargo", "build", "--release"]
    subprocess.run(command, capture_output=True)
    os.chdir(curdir)


def benchmark_r2u2_rust(n: int) -> tuple[float, float]:
    print("Checking number verdicts computed by r2u2 (Rust)")
    command = [R2U2_RUST, "run", SPEC_BIN, R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    num_verdicts = int(proc.stdout.decode().splitlines()[-1].split(":")[1].split(",")[0])

    print("Benchmarking r2u2 (Rust)")
    command = [TIME, "-v", R2U2_RUST, "run", SPEC_BIN, R2U2_TRACE]
    time_avg, mem_avg = run_command_n(command, n)
    throughput_avg = num_verdicts / time_avg
    return (throughput_avg, mem_avg)


def recompile_hydra(spec: str) -> None:
    print("Generating hydra spec")
    command = ["python3", C2PO, "--bnf", "--write-hydra", HYDRA_FILE, "-c", spec]
    subprocess.run(command, capture_output=True)


def benchmark_hydra(n: int) -> tuple[float, float]:
    print("Checking number verdicts computed by hydra")
    command = [HYDRA, HYDRA_FILE, HYDRA_TRACE]
    proc = subprocess.run(command, capture_output=True)
    num_verdicts = int(proc.stdout.decode().splitlines()[-1].split(":")[0])

    print("Running hydra")
    command = [TIME, "-v", HYDRA, HYDRA_FILE, HYDRA_TRACE]
    time_avg, mem_avg = run_command_n(command, n)
    throughput_avg = num_verdicts / time_avg
    return (throughput_avg, mem_avg)


def recompile_bvmon(spec: str, nsigs: int, word_size: int) -> None:
    print("Generating bvmon monitor")
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
        str(word_size),
        spec
    ]
    proc = subprocess.run(command, capture_output=True)

    with open(BVMON_FILE, "w") as f:
        f.write(proc.stdout.decode())

    print("Compiling bvmon monitor")
    command = [CC, "-O3", "-DOUTPUT", "-o", BVMON_BIN, BVMON_FILE]
    subprocess.run(command, capture_output=True)


def benchmark_bvmon(n: int, word_size: int) -> tuple[float, float]:
    print("Checking number verdicts computed by bvmon")
    command = [f"./{BVMON_BIN}", R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    num_verdicts = len(proc.stdout.decode().splitlines()) * word_size

    print("Running bvmon")
    command = [TIME, "-v", f"./{BVMON_BIN}", R2U2_TRACE]
    time_avg, mem_avg = run_command_n(command, n)
    throughput_avg = num_verdicts / time_avg
    return (throughput_avg, mem_avg)


def compare_output() -> None:
    print("Comparing outputs")
    command = [R2U2_C, SPEC_BIN, R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    with open(R2U2_OUTPUT, "w") as f:
        f.write(proc.stdout.decode())

    command = [HYDRA, HYDRA_FILE, HYDRA_TRACE]
    proc = subprocess.run(command, capture_output=True)
    with open(HYDRA_OUTPUT, "w") as f:
        f.write(proc.stdout.decode())

    command = [f"./{BVMON_BIN}", R2U2_TRACE]
    proc = subprocess.run(command, capture_output=True)
    with open(BVMON_OUTPUT, "w") as f:
        f.write(proc.stdout.decode())

    command = ["python3", "compare_output.py", R2U2_OUTPUT, HYDRA_OUTPUT, BVMON_OUTPUT]
    proc = subprocess.run(command)
    if proc.returncode != 0:
        print("Outputs do not match")
        sys.exit(1)
    else:
        print("Outputs match")


parser = argparse.ArgumentParser(description="Benchmarking r2u2, hydra and bvmon")
parser.add_argument(
    "benchmark",
    choices=["interval", "trace", "word-size", "specs"],
    help="Benchmark to run",
)
args = parser.parse_args()

try: 
    os.mkdir(OUTPUT_DIR)
except FileExistsError:
    pass

if args.benchmark == "trace":
    trace_len = 5_000_000
    nsigs = 1

    data = {}

    for ub in [
        # 100,
        1_000,
        1_024,
        10_000
    ]:
        spec = f"F[0,{ub}] a0\n"
        with open(SPEC_FILE, "w") as f:
            f.write(spec)

        recompile_r2u2_c(SPEC_FILE)
        recompile_r2u2_rust(SPEC_FILE)
        recompile_hydra(SPEC_FILE)
        recompile_bvmon(SPEC_FILE, nsigs, BVMON_DEFAULT_WORD_SIZE)

        for density in [
            10,
            5,
            2,
            1,
            0.75,
            0.5,
            0.25,
            0.1,
            0.05,
            0.01,
            0.005,
            0.001,
            0.0005,
            0.0001,
            0.00005,
            0.00001,
            0.000005,
            0.000001,
        ]:
            print(f"Generating random trace of len={trace_len}, density={density}")
            command = ["python3", "gen_trace.py", str(trace_len), str(nsigs), str(density), TRACE_DIR]
            proc = subprocess.run(command, capture_output=True)

            time_avg_r2u2_c, _ = benchmark_r2u2_c(10)
            time_avg_r2u2_rust, _ = benchmark_r2u2_rust(10)
            time_avg_hydra, _ = benchmark_hydra(10)
            time_avg_bvmon, _ = benchmark_bvmon(10, BVMON_DEFAULT_WORD_SIZE)

            data[density] = (
                time_avg_r2u2_c,
                time_avg_r2u2_rust,
                time_avg_hydra,
                time_avg_bvmon,
            )
            
        with open(f"{OUTPUT_DIR}/{ub}.csv", "w") as f:
            f.write("density,r2u2_c,r2u2_rust,hydra,bvmon\n")
            for density, times in data.items():
                f.write(f"{density},{times[0]},{times[1]},{times[2]},{times[3]}\n")
elif args.benchmark == "interval":
    trace_len = 5_000_000
    nsigs = 1

    data_r2u2_c = {}
    data_r2u2_rust = {}
    data_hydra = {}
    data_bvmon = {}

    print(f"Generating random trace of len={trace_len}, density=.5")
    command = ["python3", "gen_trace.py", str(trace_len), str(nsigs), "0.5", TRACE_DIR]
    proc = subprocess.run(command, capture_output=True)

    for ub in range(1,100):
        spec = f"F[0,{ub}] a0\n"
        with open(SPEC_FILE, "w") as f:
            f.write(spec)
            
        recompile_r2u2_c(SPEC_FILE)
        recompile_r2u2_rust(SPEC_FILE)
        recompile_hydra(SPEC_FILE)
        recompile_bvmon(SPEC_FILE, nsigs, BVMON_DEFAULT_WORD_SIZE)

        data_r2u2_c[ub] = benchmark_r2u2_c(25)
        data_r2u2_rust[ub] = benchmark_r2u2_rust(25)
        data_hydra[ub] = benchmark_hydra(25)
        data_bvmon[ub] = benchmark_bvmon(25, BVMON_DEFAULT_WORD_SIZE)
    
    with open(f"{OUTPUT_DIR}/interval.csv", "w") as f:
        f.write("tool,ub,time_avg,mem_avg\n")
        for ub, data in data_r2u2_c.items():
            f.write(f"r2u2_c,{ub},{data[0]},{data[1]}\n")
        for ub, data in data_r2u2_rust.items():
            f.write(f"r2u2_rust,{ub},{data[0]},{data[1]}\n")
        for ub, data in data_hydra.items():
            f.write(f"hydra,{ub},{data[0]},{data[1]}\n")
        for ub, data in data_bvmon.items():
            f.write(f"bvmon,{ub},{data[0]},{data[1]}\n")
elif args.benchmark == "word-size":
    trace_len = 5_000_000
    nsigs = 1

    data_bvmon = {}

    spec = "F[0,10] a0\n"
    with open(SPEC_FILE, "w") as f:
        f.write(spec)

    for word_size in [8, 16, 32, 64]:
        print(f"Generating random trace of len={trace_len}, density={0.5}")
        command = ["python3", "gen_trace.py", str(trace_len), str(nsigs), str(0.5), TRACE_DIR]
        proc = subprocess.run(command, capture_output=True)

        recompile_bvmon(SPEC_FILE, nsigs, word_size)
        time_avg, mem_avg = benchmark_bvmon(25, word_size)
        print(f"bvmon ({word_size}): {time_avg}, {mem_avg}")

        data_bvmon[word_size] = (
            time_avg,
            mem_avg,
        )

    with open(f"{OUTPUT_DIR}/word_size.csv", "w") as f:
        f.write("word_size,time_avg,mem_avg\n")
        for word_size, data in data_bvmon.items():
            f.write(f"{word_size},{data[0]},{data[1]}\n")
elif args.benchmark == "specs":
    trace_len = 5_000_000

    for spec,nsigs in [
        ("patterns/future.mltl", 1),
        ("patterns/until.mltl", 2),
        ("patterns/global_btwn_q_r.mltl", 3),
        ("patterns/min_duration.mltl", 1),
        ("patterns/prec_chain.mltl", 5),
    ]:
        print(f"Generating random trace of len={trace_len}, density=.5")
        command = ["python3", "gen_trace.py", str(trace_len), str(nsigs), "0.5", TRACE_DIR]
        proc = subprocess.run(command, capture_output=True)

        recompile_r2u2_c(spec)
        recompile_r2u2_rust(spec)
        recompile_hydra(spec)
        recompile_bvmon(spec, nsigs, BVMON_DEFAULT_WORD_SIZE)
        compare_output()
        data_r2u2_c = benchmark_r2u2_c(25)
        data_r2u2_rust = benchmark_r2u2_rust(25)
        data_hydra = benchmark_hydra(25)
        data_bvmon = benchmark_bvmon(25, BVMON_DEFAULT_WORD_SIZE)

        print(f"r2u2 (C): {data_r2u2_c}")
        print(f"hydra: {data_hydra}")
        print(f"bvmon: {data_bvmon}")

        with open(f"{OUTPUT_DIR}/{pathlib.Path(spec).stem}.csv", "w") as f:
            f.write("tool,throughput,mem\n")
            f.write(f"r2u2_c,{data_r2u2_c[0]},{data_r2u2_c[1]}\n")
            # f.write(f"r2u2_rust,{data_r2u2_rust[0]},{data_r2u2_rust[1]}\n")
            f.write(f"hydra,{data_hydra[0]},{data_hydra[1]}\n")
            f.write(f"bvmon,{data_bvmon[0]},{data_bvmon[1]}\n")
            