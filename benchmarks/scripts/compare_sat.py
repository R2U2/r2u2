from pathlib import Path
from glob import glob
import subprocess

MLTL_DIR = Path(__file__).parent / "benchmarks" / "random0" / "mltl"

MLTL_CONVERTER = Path(__file__).parent / "mltlsat" / "translator" / "src" / "MLTLConvertor"
Z3 = "z3"
SMT_FILE = "tmp.smt"

for mltl_file_str in glob(str(MLTL_DIR)+"/*"):
    mltl_file = Path(mltl_file_str)

    command = ["python3", "compiler/c2po.py", "-c", "-sat", "--extops", str(mltl_file)]
    print(" ".join(command))
    try:
        proc = subprocess.run(command, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        print("c2po timeout")
        continue

    c2po_output = proc.stdout.decode()
    is_sat_c2po = c2po_output.find("unsat") == -1 and c2po_output.find("sat") > -1

    with open(str(mltl_file), "r") as f:
        content = f.read().strip()

    command = [str(MLTL_CONVERTER), "-smtlib", content]
    # print(" ".join(command))
    proc = subprocess.run(command, capture_output=True)
    with open(SMT_FILE, "wb") as f:
        f.write(proc.stdout)

    command = [Z3, SMT_FILE]
    print(" ".join(command))
    try:
        proc = subprocess.run(command, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        print("mltlsat timeout")
        continue

    mltlsat_output = proc.stdout.decode()
    is_sat_mltlsat = mltlsat_output.find("unsat") == -1 and mltlsat_output.find("sat") > -1

    if is_sat_c2po != is_sat_mltlsat:
        print("fail")
        print(f"\t{is_sat_c2po} : {is_sat_mltlsat}")
    else:
        print("pass")
    