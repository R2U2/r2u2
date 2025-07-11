import resource
import sys

from c2po import log

MODULE_CODE = "UTIL"


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
    return (
        rusage_self.ru_utime
        + rusage_child.ru_utime
        + rusage_self.ru_stime
        + rusage_child.ru_stime
    )


def set_max_memory(bytes: int) -> None:
    """Set the maximum memory in bytes."""
    if sys.platform == "darwin":
        log.debug(
            MODULE_CODE,
            1,
            "macOS does not support setrlimit for RLIMIT_AS, ignoring max memory limit",
        )
        return
    
    log.debug(MODULE_CODE, 1, f"Setting max memory to {format_bytes(bytes)}")

    try:
        resource.setrlimit(resource.RLIMIT_AS, (bytes, resource.RLIM_INFINITY))
    except ValueError:
        log.warning(
            MODULE_CODE,
            "Failed to set max memory limit, provided limit is likely over current hard limit or OS does not support setrlimit for RLIMIT_AS",
        )
    except OverflowError:
        log.warning(
            MODULE_CODE,
            "Failed to set max memory limit, provided limit is likely over current hard limit or OS does not support setrlimit for RLIMIT_AS",
        )


def set_max_memory_offset(bytes: int) -> None:
    """Set the maximum memory in bytes, offset by the current memory usage. Does nothing if the offset is zero or negative."""
    if bytes <= 0:
        return

    # these values are in kilobytes
    rusage_self = resource.getrusage(resource.RUSAGE_SELF)
    rusage_child = resource.getrusage(resource.RUSAGE_CHILDREN)
    current_memory = rusage_self.ru_maxrss + rusage_child.ru_maxrss
    if sys.platform == "darwin":
        # macOS returns memory usage in bytes
        current_memory = current_memory // 1024

    log.debug(MODULE_CODE, 1, f"Current memory usage: {format_bytes(current_memory * 1024)}")

    new_memory = bytes + current_memory
    set_max_memory(new_memory)
