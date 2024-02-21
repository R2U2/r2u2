import pathlib
import os
import shutil

DEFAULT_WORKDIR_NAME = f"__workdir__.{os.getpid()}"

# need to use pid for benchmarking -- so we can run c2po many times in parallel without conflicts
DEFAULT_WORKDIR = pathlib.Path(__file__).parent / DEFAULT_WORKDIR_NAME

def setup_dir(dir: pathlib.Path) -> None:
    """Remove and create fresh WORK_DIR, print a warning if quiet is False"""
    if dir.is_file():
        os.remove(dir)
    elif dir.is_dir():
        shutil.rmtree(dir)

    os.mkdir(dir)

def cleanup_dir(dir: pathlib.Path) -> None:
    shutil.rmtree(dir)
