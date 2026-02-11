"""Module for logging.

Error messaging (source file location) are inspired by GNU error message standards (https://www.gnu.org/prep/standards/standards.html#Errors).
"""
import enum
import sys
import inspect
from typing import NamedTuple, Optional

ISSUE_URL: str = "https://github.com/R2U2/r2u2/issues"
MAJOR_VERSION: str = "4"
MINOR_VERSION: str = "1"
PATCH_VERSION: str = "0"
VERSION: str = f"{MAJOR_VERSION}.{MINOR_VERSION}.{PATCH_VERSION}"

log_level = 0
enable_quiet = False

# This is used to track the current command name for logging purposes. The command name should be
# set when a command is executed and reset when the command completes.
current_command_name: Optional[str] = None
def set_current_command_name(command_name: Optional[str]) -> None:
    global current_command_name
    current_command_name = command_name

def reset_current_command_name() -> None:
    global current_command_name
    current_command_name = None

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
    message_type: str,
    location: Optional[FileLocation],
    message: str,
) -> str:
    formatted_message = ""
    if current_command_name:
        formatted_message += f"{current_command_name}: "
    formatted_message += f"{message_type}: "
    if location:
        formatted_message += f"{location.filename}:{location.lineno}: "
    formatted_message += f"{message}\n"
    return formatted_message

def debug(
    level: int,
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    global log_level
    if level > log_level or enable_quiet:
        return
    formatted_message = format("debug", location, message)
    sys.stderr.write(formatted_message)

def warning(
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format("warning", location, message)
    sys.stderr.write(formatted_message)

def error(
    message: str,
    location: Optional[FileLocation] = None,
) -> None:
    if enable_quiet:
        return
    formatted_message = format("error", location, message)
    sys.stderr.write(formatted_message)

def internal(
    message: str,
    traceback_str: Optional[str] = None,
) -> None:
    if enable_quiet:
        return
    caller_location = inspect.stack()[1][1:3]
    caller_location = FileLocation(caller_location[0], caller_location[1])
    message_extra = ""
    if traceback_str:
        message_extra += f"\n{traceback_str}"
    message_extra += f"\nPlease report this issue with input files and command executed at {ISSUE_URL}"
    formatted_message = format("internal", caller_location, message + message_extra)
    sys.stderr.write(formatted_message)
