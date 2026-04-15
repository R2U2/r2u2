import resource
import sys
import re
import subprocess
import pathlib
from typing import Callable, Optional
from c2po import log

C2PO_SRC_DIR = pathlib.Path(__file__).parent

def check_executable(executable: str) -> bool:
    """Check if the given executable is valid."""
    if not pathlib.Path(executable).exists():
        return False
    if not pathlib.Path(executable).is_file():
        return False
    try:
        proc1 = subprocess.run([executable, "--version"], capture_output=True)
        proc2 = subprocess.run([executable, "-version"], capture_output=True)
        proc3 = subprocess.run([executable, "-v"], capture_output=True)
        return proc1.returncode == 0 or proc2.returncode == 0 or proc3.returncode == 0
    except FileNotFoundError:
        return False

def read_file(filename: str) -> Optional[str]:
    """Read the contents of a file and return it as a string."""
    try:
        with open(filename, "r") as f:
            return f.read()
    except OSError as e:
        message = re.sub(r"\[Errno \d+\] ", "", str(e))
        message = re.sub(r"No", r"no", message)
        log.error(message)
        return None

def format_bytes(bytes: int) -> str:
    """Return the given number of bytes in a human-readable format."""
    if bytes < 1024:
        return f"{bytes} bytes"
    elif bytes < 1024 * 1024:
        return f"{bytes / 1024:.2f} KB"
    elif bytes < 1024 * 1024 * 1024:
        return f"{bytes / 1024 / 1024:.2f} MB"
    else:
        return f"{bytes / 1024 / 1024 / 1024:.2f} GB"
    
def get_rusage_time() -> float:
    """Returns sum of user and system mode times for the current and child processes in seconds. See https://docs.python.org/3/library/resource.html."""
    rusage_self = resource.getrusage(resource.RUSAGE_SELF)
    rusage_child = resource.getrusage(resource.RUSAGE_CHILDREN)
    return rusage_self.ru_utime + rusage_child.ru_utime + rusage_self.ru_stime + rusage_child.ru_stime

def get_children_rusage_time() -> float:
    """Returns the user and system mode times for the child processes in seconds."""
    rusage_child = resource.getrusage(resource.RUSAGE_CHILDREN)
    return rusage_child.ru_utime + rusage_child.ru_stime

def set_max_memory(mb: int) -> Callable[[], None]:
    """Return a callable that sets the maximum memory in MB (for use with preexec_fn)."""
    if sys.platform == "darwin":
        log.debug(
            1, "macOS does not support setrlimit for RLIMIT_AS, ignoring max memory limit",
        )
        return lambda: None
    elif mb <= 0:
        return lambda: None
    else:
        bytes = mb * 1024 * 1024
        log.debug(2, f"setting max memory to {format_bytes(bytes)}")
        return lambda: resource.setrlimit(resource.RLIMIT_AS, (bytes, resource.RLIM_INFINITY))

def set_max_memory_offset(mb: int) -> Callable[[], None]:
    """Return a callable that sets the maximum memory in MB, offset by the current memory usage (for use with preexec_fn). Returns a no-op if the offset is zero or negative."""
    if mb <= 0:
        return lambda: None

    # these values are in kilobytes (or bytes on macOS)
    rusage_self = resource.getrusage(resource.RUSAGE_SELF)
    rusage_child = resource.getrusage(resource.RUSAGE_CHILDREN)
    current_memory = rusage_self.ru_maxrss + rusage_child.ru_maxrss
    if sys.platform == "darwin":
        # macOS returns memory usage in bytes, convert to kilobytes
        current_memory = current_memory // 1024

    log.debug(2, f"current memory usage: {format_bytes(current_memory * 1024)}")

    current_memory_mb = current_memory // 1024
    new_memory = mb + current_memory_mb

    return set_max_memory(new_memory)