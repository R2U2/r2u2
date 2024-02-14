"""
usage: python c2po2mltl.py path/to/r2u2prep.py
"""
import shutil
import subprocess
import sys
import os

from glob import glob
from pathlib import Path

CURDIR = Path(os.getcwd())
BENCHMARK_DIRS = [
    CURDIR / "boeing-wbs",
    CURDIR / "cysat",
    CURDIR / "fmsd17",
    CURDIR / "nasa-atc",
    CURDIR / "rv14",
    CURDIR / "utm",
]

r2u2prep = Path(sys.argv[1]).absolute()

for b in BENCHMARK_DIRS:
    os.chdir(b)
    mltl_dir = b / "mltl"
    if not mltl_dir.exists():
        mltl_dir.mkdir()
    else:
        shutil.rmtree(mltl_dir)
        mltl_dir.mkdir()

    for f in [Path(f) for f in glob("./**", recursive=True) if Path(f).suffix == ".c2po"]:
        print(f.name)
        subprocess.run([
            "python", r2u2prep, 
            "--booleanizer", "--disable-assemble", 
            "--mission-time", f.suffixes[0][2:],
            "--dump-mltl", b / "mltl" / f.with_suffix(".mltl").name,
            f])
