import re
import sys
import random
import os

from glob import glob
from pathlib import Path

CURDIR = Path(os.getcwd())
MLTLDIR = CURDIR / "mltl"
CSVDIR = CURDIR / "trace"

files: list[Path] = []
for f in glob(sys.argv[1]+"/**", recursive=True):
    file = Path(f)
    if file.suffix == ".ltlf":
        files.append(file)

formulas: dict[Path, tuple[set[str], str]] = {}
for file in files:
    with open(file, "r") as f:
        ltlf = f.read()

    props: set[str] = set()
    mltl = ltlf

    mltl = mltl.replace("&", "&&")
    mltl = mltl.replace("|", "||")
    mltl = mltl.replace("TRUE", "true")
    mltl = mltl.replace("FALSE", "false")
    mltl = mltl.replace("X", "G[1,1]")

    for m in re.finditer(r"\w+", mltl):
        p = m.group()
        if p == "G" or p == "F" or p == "M" or p.isdigit() or p == "false" or p == "true":
            continue
        props.add(p)

    formulas[file] = (props, mltl)

    new_file = file.with_stem(file.stem[:-4]) # remove .smv
    with open(MLTLDIR / new_file.with_suffix(".mltl").name, "w") as f:
        f.write("INPUT\n\t")
        f.write(",".join(props))
        f.write(": bool;\n\n")

        f.write("FTSPEC\n\t")
        f.write(mltl + ";")
        
    with open(CSVDIR / new_file.with_suffix(".random.csv").name, "w") as f:
        f.write("# ")
        f.write(",".join(props))
        f.write("\n")
        for i in range(0,100):
            row = [random.randint(0,1) for r in props]
            f.write(str(row) + "\n")

