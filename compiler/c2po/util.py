import pathlib
import os
import shutil

# need to use pid for benchmarking -- so we can run c2po many times in parallel without conflicts
WORK_DIR = pathlib.Path(__file__).parent / f"__workdir__.{os.getpid()}"

def setup_work_dir() -> None:
    """Remove and create fresh WORK_DIR, print a warning if quiet is False"""
    if WORK_DIR.is_file():
        os.remove(WORK_DIR)
    elif WORK_DIR.is_dir():
        shutil.rmtree(WORK_DIR)

    os.mkdir(WORK_DIR)

def cleanup_work_dir() -> None:
    shutil.rmtree(WORK_DIR)
