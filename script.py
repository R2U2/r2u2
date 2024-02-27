import multiprocessing as mp
from pathlib import Path
import subprocess
import glob
import csv
import sys

def write_result(result: dict) -> None:
    with open(sys.argv[3], "a") as f:
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
        csvwriter.writerow(result)


def test(cmd) -> None:
    print(" ".join(cmd))

    proc = subprocess.run(cmd, capture_output=True)

    if proc.returncode:
        print(proc.stdout.decode())
        print(proc.stderr.decode())
        write_result( {"filename": cmd[-1], "status": "err"})
        return
    
    result = {"filename": cmd[-1], "status": "ok"}

    datum = [s.split(" ")[1] for s in proc.stdout.decode().splitlines()]
    for data in datum:
        name,value = data.split("=")

        if name == "sat_check_time":
            continue

        result[name] = value
        
    write_result(result)


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
            "--timeout-egglog", "3600",
            "--timeout-sat", "3600", 
            "--debug", "1",
            file
        ] 
        for file in test_files]

    # passing None here means we use cpu_count processes
    with mp.Pool(None) as pool:
        results = pool.map(test, test_cmds)
