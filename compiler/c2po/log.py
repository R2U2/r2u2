"""Module for logging.

Error messaging (source file location) are inspired by GNU error message standards (https://www.gnu.org/prep/standards/standards.html#Errors).
"""
import enum
import sys
from typing import NamedTuple, Optional

MAINTAINER_EMAIL: str = "cgjohann@iastate.edu"

OUT = sys.stdout
ERR = sys.stderr

enable_debug = False
enable_quiet = False


class FileLocation(NamedTuple):
    filename: str
    lineno: int


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


def set_debug() -> None:
    global enable_debug
    enable_debug = True


def set_quiet() -> None:
    global enable_quiet
    enable_quiet = True


def format(
    message: str,
    level: str,
    color: Optional[Color],
    module: str,
    submodule: Optional[str] = None,
    location: Optional[FileLocation] = None,
) -> str:
    formatted_message = ""

    if module:
        formatted_message += f"[{module.replace('c2po.', '')}]"

    if color:
        formatted_message += f"[{color.value}{level}{Color.ENDC.value}]"
    else:
        formatted_message += f"[{level}]"

    if submodule:
        formatted_message += f"[{submodule}]"

    if location:
        formatted_message += f" {location.filename}:{location.lineno}:"

    formatted_message += f" {message}\n"

    return formatted_message


def debug(
    message: str,
    module: str,
    submodule: Optional[str] = None,
    location: Optional[FileLocation] = None,
) -> None:
    if not enable_debug or enable_quiet:
        return
    formatted_message = format(
        message, "DBG", Color.OKBLUE, module, submodule, location
    )
    ERR.write(formatted_message)


def warning(
    message: str,
    module: str,
    submodule: Optional[str] = None,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "WRN", Color.WARN, module, submodule, location)
    ERR.write(formatted_message)


def error(
    message: str,
    module: str,
    submodule: Optional[str] = None,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "ERR", Color.FAIL, module, submodule, location)
    ERR.write(formatted_message)


def internal(
    message: str,
    module: str,
    submodule: Optional[str] = None,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format(message, "BUG", Color.FAIL, module, submodule, location)
    ERR.write(formatted_message)
