from pathlib import Path
from glob import glob
import subprocess

ORACLE_DIR = Path(__file__).parent / "benchmarks" / "random0" / "oracle"
MLTL_DIR = Path(__file__).parent / "benchmarks" / "random0" / "mltl"

file_pairs: "list[tuple[Path, Path]]" = []

oracle_files: "list[Path]" = []
for oracle_file in glob(str(ORACLE_DIR)+"/*"):
    oracle_files.append(Path(oracle_file))

for mltl_file_str in glob(str(MLTL_DIR)+"/*"):
    mltl_file = Path(mltl_file_str)
    for oracle_file in oracle_files:
        if oracle_file.with_suffix("").name == mltl_file.with_suffix("").name:
            file_pairs.append((mltl_file,oracle_file))

for mltl,oracle in file_pairs:
    command = ["python3", "compiler/c2po.py", "-c", "-sat", "--egraph", str(mltl)]
    print(" ".join(command))
    proc = subprocess.run(command, capture_output=True)

    with open(str(oracle), "r") as f:
        content = f.read()
        is_sat_oracle = content.find("unsat") == -1 and content.find("sat") > -1
    
    c2po_output = proc.stdout.decode()
    is_sat_c2po = c2po_output.find("unsat") == -1 and c2po_output.find("sat") > -1

    if is_sat_c2po != is_sat_oracle:
        print("FAIL")
        print(f"{is_sat_oracle} : {is_sat_c2po}")