import multiprocessing as mp
from pathlib import Path
import subprocess
import glob
import csv
import sys

TIMEOUT = 3600

def test(cmd) -> dict:
    proc = subprocess.run(cmd, capture_output=True, timeout=TIMEOUT)

    if proc.returncode:
        return {"filename": cmd[-1], "status": "err"}
    
    results = {"filename": cmd[-1], "status": "ok"}

    datum = [s.split(" ")[1] for s in proc.stdout.decode().splitlines()]
    for data in datum:
        name,value = data.split("=")

        if name == "sat_check_time":
            continue

        results[name] = value

    return results


if __name__ == "__main__":
    files_path = Path(sys.argv[1])
    test_files = glob.glob(str(files_path)+"/*")

    test_cmds = [
        [
            "python3", 
            "/opt/compiler/c2po.py", 
            "-c", 
            "--workdir", sys.argv[2],
            "--egraph", 
            "--stats", 
            file
        ] 
        for file in test_files]

    # passing None here means we use cpu_count processes
    with mp.Pool(None) as pool:
        results = pool.map(test, test_cmds)

    with open(sys.argv[3], "w") as f:
        fieldnames = [
            "filename", 
            "status", 
            "equiv_result", 
            "equiv_check_time",
            "old_scq_size",
            "new_scq_size",
            "egraph_time",
        ]
        csvwriter = csv.DictWriter(f, fieldnames=fieldnames)
        for result in results:
            csvwriter.writerow(result)
