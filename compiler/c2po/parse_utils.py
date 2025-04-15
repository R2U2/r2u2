import pathlib
from typing import Optional
import re

from c2po import types, log

MODULE_CODE = "PRSO"

def parse_trace_file(
    trace_path: pathlib.Path, map_file_provided: bool
) -> tuple[int, Optional[types.SignalMapping]]:
    """Given `trace_path`, return the inferred length of the trace and, if `return_mapping` is enabled, a signal mapping."""
    with open(trace_path, "r") as f:
        content: str = f.read()

    lines: list[str] = content.splitlines()

    if len(lines) < 1:
        return (-1, None)

    cnt: int = 0
    signal_mapping: types.SignalMapping = {}

    if lines[0][0] == "#":
        # then there is a header
        header = lines[0][1:]

        if map_file_provided:
            log.warning(
                MODULE_CODE,
                "Map file given and header included in trace file; header will be ignored"
            )

        for id in [s.strip() for s in header.split(",")]:
            if id in signal_mapping:
                log.warning(
                    MODULE_CODE,
                    f"Signal ID '{id}' found multiple times in csv, using right-most value",
                    log.FileLocation(trace_path.name, 1)
                )
            signal_mapping[id] = cnt
            cnt += 1

        trace_length = len(lines) - 1

        return (trace_length, signal_mapping)

    # no header, so just return number of lines in file (i.e., number of time steps in trace)
    return (len(lines), None)


def parse_map_file(map_path: pathlib.Path) -> Optional[types.SignalMapping]:
    """Return the signal mapping from `map_path`."""
    with open(map_path, "r") as f:
        content: str = f.read()

    mapping: types.SignalMapping = {}

    lines = content.splitlines()
    for line in lines:
        if re.match(r"[a-zA-Z_][a-zA-Z0-9_\[\]]*:\d+", line):
            strs = line.split(":")
            id = strs[0]
            sid = int(strs[1])

            if id in mapping:
                log.warning(
                    MODULE_CODE,
                    f"Signal ID '{id}' found multiple times in map file, using latest value",
                    log.FileLocation(map_path.name, lines.index(line) + 1),
                )

            mapping[id] = sid
        else:
            log.error(
                MODULE_CODE,
                f"Invalid format for map line (found {line})"
                "\n\t Should be of the form SYMBOL ':' NUMERAL",
                log.FileLocation(map_path.name, lines.index(line)),
            )
            return None

    return mapping

