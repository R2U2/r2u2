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

results_path = CUR_DIR / "results.txt"


def compute_total_scq_size(
    spec_path: Path,
    enable_extops: bool,
    enable_rewrite: bool,
    enable_arity: bool,
    enable_cse: bool
) -> int:
    print(f"Computing {spec_path}")

    pickle_path = PICKLE_DIR / spec_path.with_suffix(".pickle").name

    compile(
        str(spec_path), 
        enable_booleanizer=True,
        enable_assemble=False,
        dump_ast=True,
        dump_filename=str(pickle_path),
        enable_extops=enable_extops,
        enable_rewrite=enable_rewrite,
        enable_arity=enable_arity,
        enable_cse=enable_cse,
    )

    with open(pickle_path, "rb") as f:
        control_program: C2POProgram = pickle.load(f)

    future_time_spec_section = control_program.get_future_time_spec_section()
    return future_time_spec_section.total_scq_size if future_time_spec_section else 0


if not PICKLE_DIR.is_dir():
    PICKLE_DIR.mkdir()

benchmarks = []

with results_path.open("w") as f:
    for spec_filename in glob(f"{MLTL_DIR}/**"):
        spec_path = Path(spec_filename)
        mission_time = int(spec_path.suffixes[0][2:])

        control_total_scq_size = compute_total_scq_size(
            spec_path,
            enable_extops=True,
            enable_rewrite=False,
            enable_arity=False,
            enable_cse=False
        )
        
        rewrite_total_scq_size = compute_total_scq_size(
            spec_path,
            enable_extops=True,
            enable_rewrite=True,
            enable_arity=False,
            enable_cse=False
        )
        
        cse_total_scq_size = compute_total_scq_size(
            spec_path,
            enable_extops=True,
            enable_rewrite=False,
            enable_arity=False,
            enable_cse=True
        )
        
        rewrite_cse_total_scq_size = compute_total_scq_size(
            spec_path,
            enable_extops=True,
            enable_rewrite=True,
            enable_arity=False,
            enable_cse=True
        )

        rewrite_percent_reduction = 1.0 - (rewrite_total_scq_size / control_total_scq_size)
        cse_percent_reduction = 1.0 - (cse_total_scq_size / control_total_scq_size)
        rewrite_cse_percent_reduction = 1.0 - (rewrite_cse_total_scq_size / control_total_scq_size)

        f.write(f"{spec_path.with_suffix('').stem:30},{mission_time:8},{control_total_scq_size:10},{rewrite_total_scq_size:10}, {cse_total_scq_size:10},{rewrite_cse_total_scq_size:10},{rewrite_percent_reduction:10.5f}, {cse_percent_reduction:10.5f},{rewrite_cse_percent_reduction:10.5f}\n")

        
        