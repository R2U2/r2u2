import pathlib
import os
import shutil
import resource

from c2po import log

MODULE_CODE = "UTIL"

def setup_dir(dir: pathlib.Path) -> None:
    """Remove and create fresh `dir`, print a warning if quiet is False"""
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
    return rusage_self.ru_utime + rusage_child.ru_utime + rusage_self.ru_stime + rusage_child.ru_stime

def set_max_memory(bytes: int) -> None:
    """Set the maximum memory in bytes"""
    try:
        resource.setrlimit(resource.RLIMIT_AS, (bytes, resource.RLIM_INFINITY))
    except ValueError:
        log.warning(MODULE_CODE, "Failed to set max memory limit, provided limit is over current hard limit")
