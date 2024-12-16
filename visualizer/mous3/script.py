import pathlib
import subprocess

C2PO_BIN = pathlib.Path(".") / ".." / ".." / "compiler" / "c2po.py"
R2U2_BIN = pathlib.Path(".") / ".." / ".." / "monitors" / "c" / "build" / "r2u2"

#TODO: Everything below this needs to be passed in by Main
C2PO_FILE = pathlib.Path(".") / "tests" / "tail_to_sun" / "tts.c2po"
MAP_FILE = pathlib.Path(".") / "tests" / "tail_to_sun" / "tts.map"
TRACE_DIR = pathlib.Path(".") / "tests" / "tail_to_sun" / "traces/"
CONFIG_FILE = pathlib.Path(".") / "tests" / "tail_to_sun" / "my_spec.bin"

c2po_command = ["python3", C2PO_BIN, "--booleanizer", "--map", MAP_FILE, C2PO_FILE, "--output", CONFIG_FILE]
subprocess.run(c2po_command)

r2u2_command_output = {}

for trace in TRACE_DIR.glob("*.csv"):
    r2u2_command = [R2U2_BIN, CONFIG_FILE, trace]
    ret = subprocess.run(r2u2_command, capture_output=True)

    r2u2_command_output[trace] = ret.stdout.decode()

    with open(f"file.{trace.stem}.out", "w") as f:
        f.write(ret.stdout.decode())
