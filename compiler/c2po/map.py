from typing import Any
import re
from c2po import cpt, command, util, types, log

def parse_map_file(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
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
    missing = cpt.assign_signal_ids(program, context, mapping)
    if len(missing) > 0:
        log.error(
            f"map file does not contain all signals in the program: {', '.join(missing)}",
            log.FileLocation(options['filename'], 1),
        )
        return command.ReturnCode.ERROR 

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
    func=parse_map_file,
    guards=[],
)
command.CommandRegistry.register(parse_map_command)


def generate_map(
    program: cpt.Program, context: cpt.Context, options: dict[str, Any]
) -> command.ReturnCode:
    """
    Generate a signal mapping for a given program and apply the mapping to the program. 
    If the program already has a valid signal mapping, this will only output the mapping to the map file.
    The map file will assign indices based on the order the signals are declared in the program. 

    `options` is a dictionary of options that must contain the following keys: - `output`: The path
    to the map file to write to

    Returns:
        A ReturnCode.SUCCESS if the map file was generated successfully, ReturnCode.ERROR otherwise.
    """
    output_file = options["output"]
    
    if not cpt.has_valid_signal_mapping(program, context):
        mapping: types.SignalMapping = {}
        for i, signal in enumerate(context.signals):
            mapping[signal] = i

        missing = cpt.assign_signal_ids(program, context, mapping)
        if len(missing) > 0:
            log.internal(
                f"auto-generated map file does not contain all signals in the program: {', '.join(missing)}",
            )
            return command.ReturnCode.ERROR

        context.signal_mapping = mapping

    if output_file is None:
        return command.ReturnCode.SUCCESS

    with open(output_file, "w") as f:
        for symbol, id in context.signal_mapping.items():
            f.write(f"{symbol}:{id}\n")    

    context.map_filename = output_file
    return command.ReturnCode.SUCCESS

generate_map_command = command.Command(
    name="generate_map",
    description="Generate a signal mapping for a given program. If the program already has a valid signal mapping, this will only output the mapping to the map file. The map file will assign indices based on the order the signals are declared in the program. ",
    options=[
        {
            "name": "output",
            "description": "The path to the output map file",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        }
    ],
    func=generate_map,
    guards=[command.WELL_TYPED, command.DESUGARED],
)
command.CommandRegistry.register(generate_map_command)