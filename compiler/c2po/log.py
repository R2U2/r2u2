"""Module for logging.

Error messaging (source file location) are inspired by GNU error message standards (https://www.gnu.org/prep/standards/standards.html#Errors).
"""
import enum
import sys
from typing import NamedTuple, Optional

ISSUE_URL: str = "https://github.com/R2U2/r2u2/issues"
MAJOR_VERSION: str = "4"
MINOR_VERSION: str = "0"
PATCH_VERSION: str = "0"
VERSION: str = f"{MAJOR_VERSION}.{MINOR_VERSION}.{PATCH_VERSION}"

log_level = 0
enable_quiet = False


class FileLocation(NamedTuple):
    filename: str
    lineno: int

EMPTY_FILE_LOC = FileLocation("",0)

class Color(enum.Enum):
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    OKGREEN = "\033[92m"
    WARN = "\033[93m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"

def set_log_level(level: int) -> None:
    global log_level
    log_level = level

def set_quiet() -> None:
    global enable_quiet
    enable_quiet = True


def format(
    message: str,
    level: str,
    color: Optional[Color],
    module: str,
    location: Optional[FileLocation] = None,
) -> str:
    formatted_message = ""

    if module:
        formatted_message += f"[{module.replace('c2po.', '')}]"

    if color:
        formatted_message += f"[{color.value}{level}{Color.ENDC.value}]"
    else:
        formatted_message += f"[{level}]"

    if location:
        formatted_message += f" {location.filename}:{location.lineno}:"

    formatted_message += f" {message}\n"

    return formatted_message


def debug(
    module: str,
    level: int,
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    global log_level
    if level > log_level or enable_quiet:
        return
    formatted_message = format(
        message, "DBG", Color.OKBLUE, module, location
    )
    sys.stderr.write(formatted_message)


def warning(
    module: str,
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "WRN", Color.WARN, module, location)
    sys.stderr.write(formatted_message)


def error(
    module: str,
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "ERR", Color.FAIL, module, location)
    sys.stderr.write(formatted_message)


def internal(
    module: str,
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    message_extra = f"\nPlease report this issue at {ISSUE_URL}"
    formatted_message = format(message + message_extra, "BUG", Color.FAIL, module, location)
    sys.stderr.write(formatted_message)
