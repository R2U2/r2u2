from pathlib import Path
from glob import glob
import subprocess

MLTL_DIR = Path(__file__).parent / "benchmarks" / "__random"

MLTL_CONVERTER = Path(__file__).parent / "mltlsat" / "translator" / "src" / "MLTLConvertor"
Z3 = "z3"
SMT_FILE = "tmp.smt"

for mltl_file_str in glob(str(MLTL_DIR)+"/*"):
    if mltl_file_str.find("L20") < 0:
        continue

    mltl_file = Path(mltl_file_str)

    command = ["python3", "compiler/c2po.py", "-c", "-sat", "--extops", "-dr", str(mltl_file)]
    print(" ".join(command))
    try:
        proc = subprocess.run(command, capture_output=True, timeout=300)
    except subprocess.TimeoutExpired:
        print("c2po timeout")

    c2po_output = proc.stdout.decode()

    if c2po_output.find("unsat") > -1:
        c2po_result = "unsat"
    elif c2po_output.find("sat") > -1:
        c2po_result = "sat"
    else:
        c2po_result = "unknown"

    command = [str(MLTL_CONVERTER), "-smtlib", str(mltl_file)]

    proc = subprocess.run(command, capture_output=True)

    with open(SMT_FILE, "wb") as f:
        f.write(proc.stdout)

    command = [Z3, SMT_FILE]

    print(" ".join(command))

    try:
        proc = subprocess.run(command, capture_output=True, timeout=300)
    except subprocess.TimeoutExpired:
        print("mltlsat timeout")
        continue

    mltlsat_output = proc.stdout.decode()

    if mltlsat_output.find("unsat") > -1:
        mltlsat_result = "unsat"
    elif mltlsat_output.find("sat") > -1:
        mltlsat_result = "sat"
    else:
        mltlsat_result = "unknown"

    if (c2po_result == "sat" and mltlsat_result == "unsat") or (c2po_result == "unsat" and mltlsat_result =="sat"):
        print("fail")
        print(f"\t{c2po_result} : {mltlsat_result}")
    else:
        print("pass")
        print(f"\t{c2po_result} : {mltlsat_result}")
