import subprocess
import sys

formula_file = sys.argv[1]
num_sigs = sys.argv[2]

# Generate trace
proc = subprocess.run(["python3", "gen_trace.py", "64", num_sigs, "8"], capture_output=True)

proc = subprocess.run(["python3", "../compiler/c2po.py", "--bvmon", "--bvmon-word-size", "8", "-c", formula_file], capture_output=True)
with open("bvmon.c", "wb") as f:
    content = f.write(proc.stdout)
proc = subprocess.run(["gcc", "-DOUTPUT", "-o", "bvmon", "bvmon.c"])
proc = subprocess.run(["./bvmon", "trace.bvmon.log"], capture_output=True)
with open("trace.bvmon.log", "wb") as f:
    content = f.write(proc.stdout)

    

