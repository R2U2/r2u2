from glob import glob
from pathlib import Path
import sys
import pickle

from c2po.main import compile
from c2po.ast import C2POProgram

sys.setrecursionlimit(10000)

CUR_DIR = Path(__file__).parent.parent

BENCHMARKS = [
    # "boeing-wbs", 
    # "nasa-atc", 
    "fmsd17", 
    # "rv14", 
    # "utm"
]

BENCHMARK_DIRS = [CUR_DIR / benchmark for benchmark in BENCHMARKS]
MLTL_DIRS = [CUR_DIR / benchmark / "mltl" for benchmark in BENCHMARKS]
PICKLE_DIRS = [CUR_DIR / benchmark / "pickle" for benchmark in BENCHMARKS]
RESULTS_PATHS = [CUR_DIR / benchmark / "results.csv" for benchmark in BENCHMARKS]

def compute_total_scq_size(
    spec_path: Path,
    pickle_dir: Path,
    mission_time: int,
    enable_extops: bool,
    enable_rewrite: bool,
    enable_arity: bool,
    enable_cse: bool
) -> int:
    print(f"Computing {spec_path}")

    spec_name = spec_path.stem + \
            (".rewrite" if enable_rewrite else "") + \
            (".cse" if enable_cse else "") + \
            (".arity" if enable_arity else "") + \
            ".pickle"
    pickle_path = pickle_dir / spec_name

    compile(
        str(spec_path), 
        custom_mission_time=mission_time,
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


for (benchmark_dir, mltl_dir, pickle_dir, results_path) in zip(BENCHMARK_DIRS, MLTL_DIRS, PICKLE_DIRS, RESULTS_PATHS):
    if not pickle_dir.is_dir():
        pickle_dir.mkdir()

    results_rows = []

    with results_path.open("w") as f:
        for spec_filename in mltl_dir.glob("*"):
            spec_path = Path(spec_filename)
            print(spec_path)
            mission_time = int(spec_path.suffixes[0][2:])

            control_total_scq_size = compute_total_scq_size(
                spec_path,
                pickle_dir,
                mission_time,
                enable_extops=True,
                enable_rewrite=False,
                enable_arity=False,
                enable_cse=False
            )
            
            rewrite_total_scq_size = compute_total_scq_size(
                spec_path,
                pickle_dir,
                mission_time,
                enable_extops=True,
                enable_rewrite=True,
                enable_arity=False,
                enable_cse=False
            )
            
            cse_total_scq_size = compute_total_scq_size(
                spec_path,
                pickle_dir,
                mission_time,
                enable_extops=True,
                enable_rewrite=False,
                enable_arity=False,
                enable_cse=True
            )
            
            rewrite_cse_total_scq_size = compute_total_scq_size(
                spec_path,
                pickle_dir,
                mission_time,
                enable_extops=True,
                enable_rewrite=True,
                enable_arity=False,
                enable_cse=True
            )

            rewrite_percent_reduction = 1.0 - (rewrite_total_scq_size / control_total_scq_size)
            cse_percent_reduction = 1.0 - (cse_total_scq_size / control_total_scq_size)
            rewrite_cse_percent_reduction = 1.0 - (rewrite_cse_total_scq_size / control_total_scq_size)

            f.write(f"{spec_path.with_suffix('').stem:40},{mission_time:8},{control_total_scq_size:10},{rewrite_total_scq_size:10}, {cse_total_scq_size:10},{rewrite_cse_total_scq_size:10},{rewrite_percent_reduction:10.5f}, {cse_percent_reduction:10.5f},{rewrite_cse_percent_reduction:10.5f}\n")

            
            