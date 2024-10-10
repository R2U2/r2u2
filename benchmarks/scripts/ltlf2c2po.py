"""
Used to adapt MLTL-sat artifact (https://temporallogic.org/research/CAV19/artifact.tar.xz) to C2PO input. Recurses thru argument directory, turns files with '.smv.ltlf' extensions to ones with '.mltl' extensions suitable as input to C2PO.

usage:python ltlf2mltl.py path/to/dir mission-time
"""
import re
import sys
import os

from typing import List, Dict, Tuple, Set
from glob import glob
from pathlib import Path

CURDIR = Path(os.getcwd())
MLTLDIR = CURDIR / "mltl"

files: List[Path] = []
for f in glob(sys.argv[1]+"/**", recursive=True):
    file = Path(f)
    if file.suffix == ".ltlf":
        files.append(file)

formulas: Dict[Path, Tuple[Set[str], str]] = {}
for file in files:
    with open(file, "r") as f:
        ltlf = f.read()

    props: Set[str] = set()
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

    new_file = file.with_name(file.name[:-4]) # remove .smv
    with open(MLTLDIR / new_file.with_suffix(f".M{sys.argv[2]}.mltl").name, "w") as f:
        f.write("INPUT\n\t")
        f.write(",".join(props))
        f.write(": bool;\n\n")

        f.write("FTSPEC\n\t")
        f.write(mltl + ";")

