from glob import glob
import os
from pathlib import Path
import sys
from typing import List
import pickle

from c2po.main import compile
from c2po.ast import C2POProgram

sys.setrecursionlimit(10000)

CUR_DIR = Path(__file__).parent
MLTL_DIR = CUR_DIR / "mltl"
PICKLE_DIR = CUR_DIR / "pickle"

if not PICKLE_DIR.is_dir():
    PICKLE_DIR.mkdir()

benchmarks = []

spec_paths: List[Path] = []
for spec in glob(f"{MLTL_DIR}/**"):
    spec_path = Path(spec)
    spec_paths.append(spec_path)
    mission_time = int(spec_path.suffixes[0][2:])

for spec_path in spec_paths:
    pickle_path = PICKLE_DIR / spec_path.with_suffix(".pickle").name
    compile(
        str(spec_path), 
        enable_booleanizer=True,
        enable_assemble=False,
        dump_ast=True,
        dump_filename=str(pickle_path),
        enable_extops=True,
        enable_rewrite=False,
        enable_arity=False,
        enable_cse=False,
    )

    with open(pickle_path, "rb") as f:
        control_program: C2POProgram = pickle.load(f)

    future_time_spec_section = control_program.get_future_time_spec_section()
    if future_time_spec_section:
        print(future_time_spec_section.total_scq_size)
    