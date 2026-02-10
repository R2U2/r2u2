from typing import Any
import random   
from c2po import cpt, command, types, util, log

def parse_trace_file(
    program: cpt.Program,
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
    if lines[0][0] != "#":
        # no header, so just set trace length
        context.trace_length = len(lines)
        return command.ReturnCode.SUCCESS

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
    missing = cpt.assign_signal_ids(program, context, signal_mapping)
    if len(missing) > 0:
        log.error(
            f"trace file does not contain all signals in the program: {', '.join(missing)}",
            log.FileLocation(options['trace_filename'], 1),
        )
        return command.ReturnCode.ERROR

    context.trace_length = len(lines) - 1
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
    func=parse_trace_file,
    guards=[],
)
command.CommandRegistry.register(parse_trace_command)

def generate_trace(program: cpt.Program, context: cpt.Context, options: dict[str, Any]) -> command.ReturnCode:
    """
    Generate a random trace for a given program and attaches it to the context.

    `options` is a dictionary of options that must contain the following keys:
    - `length`: The length of the trace
    - `min`: The minimum value for numeric types
    - `max`: The maximum value for numeric types
    - `output`: The path to the output trace file
    - `print`: Whether to print the trace to the console

    Returns:
        A ReturnCode.SUCCESS if the trace was generated successfully, ReturnCode.ERROR otherwise.
        If the trace was generated successfully, the trace will be attached to the context.
    """
    length = options["length"]
    min_val = options["min"]
    max_val = options["max"]
    seed = options["seed"]
    output_file = options["output"]
    print_trace = options["print"]
    float_precision = options["float_precision"] + 2

    if seed is not None:
        random.seed(seed)

    log.debug(1, f"generating trace of length {length}...")
    start_time = util.get_rusage_time()

    variables: list[tuple[str, types.Type]] = sorted(
        list(context.signals.items()), key=lambda x: context.signal_mapping[x[0]]
    )

    output_lines = [f"#{','.join(var_name for var_name, _ in variables)}"]
    for _ in range(length):
        output_lines.append(
            ','.join(
                str(random.randint(0, 1)) 
                if types.is_bool_type(var_type)
                else str(random.uniform(min_val, max_val))[:float_precision]
                if types.is_float_type(var_type)
                else str(random.randint(int(min_val), int(max_val)))
                for _, var_type in variables
            )
        )

    end_time = util.get_rusage_time()
    log.debug(1, f"trace generated in {end_time - start_time} seconds")

    context.trace = output_lines

    if output_file is not None:
        with open(output_file, "w") as f:
            f.write("\n".join(output_lines))

    if print_trace:
        print("\n".join(output_lines))

    return command.ReturnCode.SUCCESS

generate_trace_command = command.Command(
    name="generate_trace",
    description="Generate a random trace for a given program.",
    func=generate_trace,
    options=[
        {
            "name": "length",
            "description": "The length of the trace",
            "required": True,
            "type": int,
            "default": 10,
            "choices": None,
        },
        {
            "name": "min",
            "description": "The minimum value for numeric types",
            "required": True,
            "type": float,
            "default": 0.0,
            "choices": None,
        },
        {
            "name": "max",
            "description": "The maximum value for numeric types",
            "required": True,
            "type": float,
            "default": 100.0,
            "choices": None,
        },
        {
            "name": "seed",
            "description": "The seed for the random number generator",
            "required": False,
            "type": int,
            "default": None,
            "choices": None,
        },
        {
            "name": "float-precision",
            "description": "The number of decimal places for floating point numbers",
            "required": False,
            "type": int,
            "default": 5,
            "choices": None,
        },
        {
            "name": "output",
            "description": "The path to the output trace file",
            "required": False,
            "type": str,
            "default": None,
            "choices": None,
        },
        {
            "name": "print",
            "description": "Whether to print the trace to the console",
            "required": False,
            "type": bool,
            "default": False,
            "choices": None,
        },
    ],
    guards=[command.VALID_SIGNAL_MAPPING]
)
command.CommandRegistry.register(generate_trace_command)
