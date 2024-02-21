import pathlib
import os
import shutil
import resource

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

def get_rusage_time() -> float:
    """Returns sum of user and system mode times for the current and child processes in seconds. See https://docs.python.org/3/library/resource.html."""
    rusage_self = resource.getrusage(resource.RUSAGE_SELF)
    rusage_child = resource.getrusage(resource.RUSAGE_CHILDREN)
    return rusage_self[0] + rusage_child[0] + rusage_self[1] + rusage_child[1]
