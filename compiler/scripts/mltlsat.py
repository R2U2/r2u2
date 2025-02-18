import multiprocessing as mp
from pathlib import Path
import argparse
import subprocess
import glob
import csv

C2PO_PATH: str = "../c2po.py"
output_filename: str = ""

def write_result(result: dict) -> None:
    global output_filename
    with open(output_filename, "a") as f:
        fieldnames = [
            "filename", 
            "status", 
            "sat_result", 
            "sat_time",
            "num_sat_calls",
        ]
        csvwriter = csv.DictWriter(f, fieldnames=fieldnames)
        csvwriter.writerow(result)


def test(cmd) -> None:
    print(" ".join(cmd))

    proc = subprocess.run(cmd, capture_output=True)

    if proc.returncode:
        print(proc.stdout.decode())
        print(proc.stderr.decode())
        write_result( {"filename": cmd[-1], "status": "err"})
        return
    
    result = {"filename": cmd[2], "status": "ok"}

    datum = [s.split(" ")[1] for s in proc.stdout.decode().splitlines()]
    for data in datum:
        name,value = data.split("=")
        result[name] = value
        
    write_result(result)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("filedir", help="directory with test files (.mltl)")
    parser.add_argument("solver", choices={"z3","cvc5","bitwuzla","yices2","mathsat5"}, help="smt solver to use")
    parser.add_argument("encoding", choices={"uflia", "aufbv", "qf_aufbv", "qf_bv", "qf_bv_incr"}, help="encodong to use for smt solver")
    parser.add_argument("output", help="file to write output to")
    parser.add_argument("--solver-option", action="append", default=[], help="options to pass to smt solver")
    parser.add_argument("--eqsat", help="enable equality saturation", action="store_true")
    parser.add_argument("--timeout-sat", default=3600, type=int, help="timeout for smt solver")
    parser.add_argument("--timeout-eqsat", default=3600, type=int, help="timeout for eqsat")
    parser.add_argument("--debug", action="store_true", help="run c2po with debug flag")
    args = parser.parse_args()

    files_path = Path(args.filedir)
    test_files = glob.glob(str(files_path)+"/*")

    output_filename = args.output

    test_cmds = [
        [
            "python3", 
            C2PO_PATH, 
            file,
            "-c", 
            "--no-cse",
            "--extops", 
            "--sat", 
            "--timeout-sat", str(args.timeout_sat), 
            "--timeout-eqsat", str(args.timeout_eqsat), 
            "--smt-path", args.solver,
            "--smt-encoding", args.encoding,
            "--stats", 
        ] + [f"--smt-option=\"{option}\"" for option in args.solver_option] + (["--eqsat"] if args.eqsat else []) + (["--debug"] if args.debug else [])
        for file in test_files
    ]

    # passing None here means we use cpu_count processes
    with mp.Pool(None) as pool:
        results = pool.map(test, test_cmds)
