import re
from typing import Any
from c2po import types, log, command, cpt, util

def parse_trace_file(
    context: cpt.Context,
    options: dict[str, Any]
) -> command.ReturnCode:
    """
    Parse a trace file and store the signal mapping and trace length in the context.

    `options` is a dictionary of options that must contain the following key:
    - `filename`: The path to the trace file

    Returns:
        A ReturnCode.SUCCESS if the trace file was parsed successfully, ReturnCode.ERROR otherwise. 
        If the trace file was parsed successfully, the signal mapping and trace length will be stored in the context.
    """
    content = util.read_file(options["filename"])
    if content is None:
        return command.ReturnCode.ERROR
        
    context.trace_filename = options["filename"]

    lines: list[str] = content.splitlines()
    if len(lines) < 1:
        log.error(
            "trace file is empty",
            log.FileLocation(options['filename'], 1)
        )
        return command.ReturnCode.ERROR

    cnt: int = 0
    signal_mapping: types.SignalMapping = {}
    if lines[0][0] == "#":
        # then there is a header
        header = lines[0][1:]

        if options.get('map_filename') is not None:
            log.warning(
                "map file given and header included in trace file; header will be ignored",
            )

        for id in [s.strip() for s in header.split(",")]:
            if id in signal_mapping:
                log.warning(
                    f"signal '{id}' found multiple times in csv, using right-most value",
                    log.FileLocation(options['trace_filename'], 1)
                )
            signal_mapping[id] = cnt
            cnt += 1

        context.signal_mapping = signal_mapping
        context.trace_length = len(lines) - 1
        return command.ReturnCode.SUCCESS

    # no header, so just set trace length
    context.trace_length = len(lines)
    return command.ReturnCode.SUCCESS

parse_trace_command = command.Command(
    name="parse_trace",
    description="Parse a trace file and add the signal mapping and trace length to the context",
    options=[
        {
            "name": "filename",
            "description": "The path to the trace file",
            "required": True,
            "type": str,
            "default": None,
            "choices": None,
        }
    ],
    func=lambda program, context, options: parse_trace_file(context, options),
    guards=[],
)
command.CommandRegistry.register(parse_trace_command)

def parse_map_file(context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Parse a map file and add the signal mapping to the context.

    `options` is a dictionary of options that must contain the following keys:
    - `filename`: The path to the map file

    Returns:
        A ReturnCode.SUCCESS if the map file was parsed successfully, ReturnCode.ERROR otherwise. If the map file was parsed successfully, the signal mapping will be stored in the context.
    """
    content = util.read_file(options["filename"])
    if content is None:
        return command.ReturnCode.ERROR

    context.map_filename = options["filename"]

    mapping: types.SignalMapping = {}
    lines = content.splitlines()
    for line in lines:
        if re.match(r"[a-zA-Z_][a-zA-Z0-9_\[\]]*:\d+", line):
            strs = line.split(":")
            id = strs[0]
            sid = int(strs[1])

            if id in mapping:
                log.warning(
                    f"signal '{id}' found multiple times in map file, using latest value",
                    log.FileLocation(options['filename'], lines.index(line) + 1),
                )

            mapping[id] = sid
        else:
            log.error(
                f"invalid format for map line (found {line}), should be of the form SYMBOL ':' NUMERAL",
                log.FileLocation(options['filename'], lines.index(line) + 1),
            )
            return command.ReturnCode.ERROR

    context.signal_mapping = mapping
    options['map_filename'] = options['filename']
    return command.ReturnCode.SUCCESS

parse_map_command = command.Command(
    name="parse_map",
    description="Parse a map file and add the signal mapping to the context",
    options=[
        {
            "name": "filename",
            "description": "The path to the map file",
            "required": True,
            "type": str,
            "default": None,
            "choices": None,
        } 
    ],
    func=lambda program, context, options: parse_map_file(context, options),
    guards=[],
)
command.CommandRegistry.register(parse_map_command)
