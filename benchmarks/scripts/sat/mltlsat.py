import multiprocessing as mp
from pathlib import Path
import argparse
import subprocess
import glob
import csv

# FIXME: always make sure this is "/opt/compiler/c2po.py" before building container
C2PO_PATH: str = "/opt/compiler/c2po.py"

output_filename: str = ""
debug: bool = False


def write_result(result: dict) -> None:
    global output_filename
    with open(output_filename, "a") as f:
        fieldnames = [
            "filename",
            "status",
            "smt_encoding_time",
            "sat_result",
            "sat_time",
            "num_sat_calls",
        ]
        csvwriter = csv.DictWriter(f, fieldnames=fieldnames)
        csvwriter.writerow(result)


def test(cmd) -> None:
    global debug
    print(" ".join(cmd))

    proc = subprocess.run(cmd, capture_output=True)

    if proc.returncode:
        print(proc.stdout.decode())
        print(proc.stderr.decode())
        write_result({"filename": cmd[2], "status": "err"})
        return
    
    if debug:
        print(proc.stdout.decode())
        print(proc.stderr.decode())

    result = {"filename": cmd[2], "status": "ok"}

    datum = [s.split(" ")[1] for s in proc.stdout.decode().splitlines() if "STAT" in s]
    for data in datum:
        name, value = data.split("=")
        result[name] = value

    write_result(result)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("filedir", help="directory with test files (.mltl)")
    parser.add_argument(
        "solver",
        help="smt solver to use",
    )
    parser.add_argument(
        "encoding",
        help="encodong to use for smt solver",
    )
    parser.add_argument("output", help="file to write output to")
    parser.add_argument(
        "--solver-option",
        action="append",
        default=[],
        help="options to pass to smt solver",
    )
    parser.add_argument(
        "--eqsat", help="enable equality saturation", action="store_true"
    )
    parser.add_argument(
        "--smt-max-time", default=1200, type=int, help="timeout for smt solver"
    )
    parser.add_argument(
        "--eqsat-max-time", default=1200, type=int, help="timeout for eqsat"
    )
    parser.add_argument(
        "--smt-max-memory", default=0, type=int, help="max memory for smt solver, 0 for no limit (in MB)"
    )
    parser.add_argument(
        "--eqsat-max-memory", default=0, type=int, help="max memory for eqsat, 0 for no limit (in MB)"
    )
    parser.add_argument(
        "--nprocs", type=int, help="number of processes to use"
    )
    parser.add_argument("--debug", action="store_true", help="run c2po with debug flag")
    args = parser.parse_args()

    files_path = Path(args.filedir)
    test_files = glob.glob(str(files_path) + "/*")

    output_filename = args.output
    debug = args.debug

    test_cmds = [
        [
            "python3",
            C2PO_PATH,
            file,
            "-c",
            "--extops",
            "--check-sat",
            "--smt-max-time",
            str(args.smt_max_time),
            "--eqsat-max-time",
            str(args.eqsat_max_time),
            "--smt-max-memory",
            str(args.smt_max_memory),
            "--eqsat-max-memory",
            str(args.eqsat_max_memory),
            "--smt-solver",
            args.solver,
            "--smt-encoding",
            args.encoding,
            "--stats",
        ]
        + [f'--smt-option="{option}"' for option in args.solver_option]
        + (["--eqsat"] if args.eqsat else [])
        + (["--debug"] if args.debug else [])
        for file in test_files
    ]

    # passing None here means we use cpu_count processes
    with mp.Pool(args.nprocs) as pool:
        results = pool.map(test, test_cmds)
