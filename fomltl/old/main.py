"""
This script runs a number of MLTL^FO formulas over R2U2.

The input trace format is a bit different from usual. Each column

For each c2po spec, input trace, oracle trace triple:
1. Compiles r2u2 spec from c2po spec
2. For each time step in the input trace:
    a. Runs r2u2 over the
3. Compares output against the oracle
"""
import pathlib
import subprocess
import re

FILE_PATH = pathlib.Path(__file__)
FILE_DIR = FILE_PATH.parent

C2PO_PATH = FILE_DIR / ".." / "compiler" / "c2po.py"
R2U2_PATH = FILE_DIR / ".." / "monitors" / "static" / "build" / "r2u2"


def run_c2po(spec: pathlib.Path, map: pathlib.Path, output: pathlib.Path) -> int:
    command = [
        "python3",
        str(C2PO_PATH),
        str(spec),
        "--map",
        str(map),
        "-bz",
        "-o",
        str(output),
    ]
    proc = subprocess.run(command)
    return proc.returncode


def run_r2u2(spec: pathlib.Path, trace: pathlib.Path, output: pathlib.Path) -> int:
    command = [str(R2U2_PATH), str(spec), str(trace)]
    proc = subprocess.run(command, capture_output=True, text=True)

    if proc.returncode != 0:
        return proc.returncode

    with open(output, "w") as f:
        f.write(proc.stdout)
    return proc.returncode


def gen_r1_c2po(n: int) -> str:
    struct_section = (
        "STRUCT\n"
        "Task: {\n"
        "sched,exec: bool;\n"
        "};\n"
    )

    input_section = (
         "INPUT\n"
        f"Scheduled: bool[{n}];\n"
        f"Exec: bool[{n}];\n"
    )

    define_section = (
        "DEFINE\n"
        "Sched := {\n" +
        ",\n".join([f"Task(Scheduled[{i}], Exec[{i}])" for i in range(0,n)]) +
        "\n"
        "};\n"
    )

    ftspec_section = (
        "FTSPEC\n"
        "-- Each task in the scheduler shall execute within the next 5 seconds.\n"
        "R1: foreach(t : Sched)(t.sched -> F[0,5] t.exec);\n"
    )

    return struct_section + input_section + define_section + ftspec_section


def process_map_file(map_path: pathlib.Path) -> "dict[str,int]":
    """Return the signal mapping from `map_path`."""
    with open(map_path, "r") as f:
        content: str = f.read()

    mapping: dict[str,int] = {}

    lines = content.splitlines()
    for line in lines:
        if re.match("[a-zA-Z_]\\w*:\\d+", line):
            strs = line.split(":")
            id = strs[0]
            sid = int(strs[1])

            if id in mapping:
                print(f"Signal '{id}' found multiple times in map file, using last value")

            mapping[id] = sid
        else:
            print(f"Invalid format for map line (found {line})")
            return {}

    return mapping


def fotrace2stdtrace(fotrace: str, mapping: "dict[str, int]") -> str:
    """Takes the content of a .trc file and translates to a standard MLTL .csv file. This conversion enforces a selection policy and checks set sizes for violations.

    Format of .trc file:
        <trace file> ::= <header> | <line>+

        <header> ::= "#" ( <symbol> | <symbol> "[" <int> "]" )+

        <int> ":" <symbol> ":" <int> ":" <bool|int|float> |
        <int> ":" <symbol> ":" <bool|int|float>
    """
    for line in fotrace.splitlines():
        if line[0] == "#":
            # header
            for var in line.split():
                if var == "#":
                    continue
                elif re.match(r"\s+\[\d+\]", var):
                    symbol = re.search(r"\s+(?<=\[)", var)
                    size = re.search(r"\d+(?<=\])", var)
                    if not symbol or not size:
                        raise ValueError
                else:
                    symbol = var
            continue

        # regular line
        values = line.split(":")
        if len(values) == 3:
            pass
        else:
            pass

    return ""


if __name__ == "__main__":
    s = gen_r1_c2po(10)
    print(s)
