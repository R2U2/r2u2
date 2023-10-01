from __future__ import annotations
from pathlib import Path
from typing import Dict, List, Optional, Tuple
import re

from .logger import logger, Color
from .ast import *
from .parse import parse
from .wcet import *
from .type_check import type_check
from .transform import *
from .assemble import *


class ReturnCode(Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_INPUT = 5
    FILE_IO_ERR  = 6


# AT_FILTER_TABLE: Dict[str, Tuple[List[C2POType], C2POType]] = {
#     "rate": ([C2POFloatType(False)], C2POFloatType(False)),
#     "movavg": ([C2POFloatType(False),C2POIntType(True)], C2POFloatType(False)),
#     "abs_diff_angle": ([C2POFloatType(False),C2POFloatType(True)], C2POFloatType(False))
# }


def process_trace_file(trace_path: Path, map_file_provided: bool) -> Tuple[int, Optional[SignalMapping]]:
    """Given `trace_path`, return the inferred length of the trace and, if `return_mapping` is enabled, a signal mapping."""
    with open(trace_path,"r") as f:
        content: str = f.read()

    lines: List[str] = content.splitlines()

    if len(lines) < 1:
        return (-1, None)

    cnt: int = 0
    signal_mapping: SignalMapping = {}

    if lines[0][0] == "#":
        # then there is a header
        header = lines[0][1:]

        if map_file_provided:
            logger.warning("Map file given and header included in trace file; header will be ignored.")

        for id in [s.strip() for s in header.split(",")]:
            if id in signal_mapping:
                logger.warning(f"{trace_path.name}:{1}: Signal ID '{id}' found multiple times in csv, using right-most value.")
            signal_mapping[id] = cnt
            cnt += 1

        trace_length = len(lines) - 1

        return (trace_length, signal_mapping)

    # no header, so just return number of lines in file (i.e., number of time steps in trace)
    return (len(lines), None)


def process_map_file(map_path: Path) -> Optional[SignalMapping]:
    """Given `trace_path`, return the inferred mission time and, if `return_mapping` is enabled, a signal mapping."""
    with open(map_path, "r") as f:
        content: str = f.read()

    mapping: SignalMapping = {}

    lines = content.splitlines()
    for line in lines:
        if re.match("[a-zA-Z_]\\w*:\\d+", line):
            strs = line.split(":")
            id = strs[0]
            sid = int(strs[1])

            if id in mapping:
                logger.warning(f"{map_path.name}:{lines.index(line)+1}: Signal ID '{id}' found multiple times in map file, using latest value.")

            mapping[id] = sid
        else:
            logger.error(f"{map_path.name}:{lines.index(line)}: Invalid format for map line (found {line})\n\t Should be of the form SYMBOL ':' NUMERAL")
            return None

    return mapping


def validate_input(
    input_filename: str, 
    trace_filename: str, 
    map_filename: str,
    output_filename: str,
    impl_str: str, 
    custom_mission_time: int,
    int_width: int, 
    int_is_signed: bool, 
    float_width: int,
    enable_atomic_checkers: bool = False,
    enable_booleanizer: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_rewrite: bool = False,
    enable_arity: bool = False,
    enable_cse: bool = False,
    enable_assemble: bool = True
) -> Tuple[bool, Optional[Path], Optional[Path], int, SignalMapping, Set[C2POTransform]]:
    """Validate the input options/files. Checks for option compatibility, file existence, and sets certain options. 
    
    Returns:
        A tuple with the following item types/descriptions:
        `bool`: validation status
        `Optional[Path]`: path corresponding to `input_filename` if it is a valid file, `None` otherwise
        `Optional[Path]`: path corresponding to `output_filename` if it is a valid file, `None` otherwise
        `int`: mission time, either set to `custom_mission_time` or the input trace length if not provided
        `Optional[SignalMapping]`: signal mapping if it was derived from `trace_filename` or `map_filebame`, `None` otherwise
        `Set[C2POTransform]`: set of transforms to apply to the input
    """
    status: bool = True

    input_path = Path(input_filename)
    if not input_path.is_file():
        logger.error(f"Input file '{input_filename} not a valid file.'")
        input_path = None

    trace_path = None
    if trace_filename != "":
        trace_path =  Path(trace_filename)
        if not trace_path.is_file():
            logger.error(f"Trace file '{trace_filename}' is not a valid file.")

    map_path = None
    if map_filename != "":
        map_path =  Path(map_filename)
        if not map_path.is_file():
            logger.error(f"Map file '{map_filename}' is not a valid file.")

    output_path = None
    if output_filename != "":
        output_path = Path(output_filename)
        if output_path.is_file():
            logger.warning(f"Output file '{output_filename}' already exists.")

    signal_mapping: Optional[SignalMapping] = None
    mission_time, trace_length = -1, -1

    if trace_path:
        (trace_length, signal_mapping) = process_trace_file(trace_path, map_path is not None)
    if map_path:
        signal_mapping = process_map_file(map_path)

    if not signal_mapping:
        signal_mapping = {}

    if custom_mission_time > -1:
        mission_time = custom_mission_time

        # warn if the given trace is shorter than the defined mission time
        if trace_length > -1 and trace_length < custom_mission_time:
            logger.warning(f"Trace length is shorter than given mission time ({trace_length} < {custom_mission_time}).")
    else:
        mission_time = trace_length

    impl: R2U2Implementation = str_to_r2u2_implementation(impl_str)
    set_types(impl, int_width, int_is_signed, float_width)

    if enable_booleanizer and enable_atomic_checkers:
        logger.error(f"Only one of AT and booleanizer can be enabled")
        status = False
    
    if impl == R2U2Implementation.C:
        if not ((not enable_booleanizer and enable_atomic_checkers) or (enable_booleanizer and not enable_atomic_checkers)):
            logger.error(f"Exactly one of booleanizer or atomic checker must be enabled for C implementation.")
            status = False
    else: # impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL
        if enable_booleanizer:
            logger.error(f"Booleanizer only available for C implementation.")
            status = False

    if impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL:
        if enable_extops:
            logger.error(f"Extended operators only support for C implementation.")
            status = False

    if enable_nnf and enable_bnf:
        logger.warning(f"Attempting rewrite to both NNF and BNF, defaulting to NNF.")

    transforms = set(TRANSFORM_PIPELINE)
    if not enable_rewrite:
        transforms.remove(optimize_rewrite_rules)
    if enable_extops:
        transforms.remove(transform_extended_operators)
    if not enable_nnf:
        transforms.remove(transform_negative_normal_form)
    if not enable_bnf:
        transforms.remove(transform_boolean_normal_form)
    if not enable_arity:
        transforms.remove(optimize_operator_arity)
    if not enable_cse:
        transforms.remove(optimize_cse)

    return (status, input_path, output_path, mission_time, signal_mapping, transforms)


def compile(
    input_filename: str,
    trace_filename: str = "",
    map_filename: str = "",
    output_filename: str = "spec.bin",
    impl: str = "c",
    custom_mission_time: int = -1,
    int_width: int = 8,
    int_signed: bool = False,
    float_width: int = 32,
    enable_atomic_checkers: bool = False,
    enable_booleanizer: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_rewrite: bool = False,
    enable_arity: bool = False,
    enable_cse: bool = False,
    enable_assemble: bool = True,
    dump_ast: bool = False,
    quiet: bool = False
) -> ReturnCode:
    """Compile a C2PO input file, output generated R2U2 binaries and return error/success code.

    Compilation stages:
    1. Input validation
    2. Parser
    3. Type checker
    4. Required transformations
    5. Option-based transformations
    6. Optimizations
    7. Assembly
    
    Args:
        input_filename: Name of a C2PO input file
        trace_filename:
        map_filename:
        output_filename: Name of binary output file
        impl: An R2U2 implementation to target. Should be one of `c`, `c++`, `cpp`, `fpga`, or `vhdl`
        int_width: Width to set C2POIntType to. Should be one of 8, 16, 32, or 64
        mission_time: Value of mission-time to replace `M` with in specs
        int_signed: If true sets C2POIntType to signed
        float_width: Width to set C2POFloatType to. Should be one of 32 or 64
        enable_atomic_checkers: If true enables Atomic Checker instructions
        enable_booleanizer: If true enables Booleanizer instructions
        enable_extops: If true enables TL extended operators (or, implies, future, release)
        enable_nnf: If true enables negation normal form of MLTL
        enable_bnf: If true enables boolean normal form of MLTL
        enable_rewrite: If true enables MLTL rewrite rule optimizations
        enable_arity: If true enables operator arity optimization
        enable_cse: If true enables Common Subexpression Elimination
        enable_assemble: If true outputs binary to output_filename
        dump_ast:
        quiet: If true disables assembly output to stdout
    """
    # ----------------------------------
    # Input validation
    # ----------------------------------
    (status, input_path, output_path, mission_time, signal_mapping, enabled_transforms) = validate_input(
        input_filename, 
        trace_filename, 
        map_filename, 
        output_filename,
        impl, 
        custom_mission_time,
        int_width, 
        int_signed, 
        float_width, 
        enable_atomic_checkers,
        enable_booleanizer,
        enable_extops,
        enable_nnf,
        enable_bnf,
        enable_rewrite,
        enable_arity,
        enable_cse,
        enable_assemble
    )

    if not status or not input_path:
        logger.error("Input invalid.")
        return ReturnCode.INVALID_INPUT

    # ----------------------------------
    # Parse
    # ----------------------------------
    program: Optional[C2POProgram] = parse(input_path)

    if not program:
        logger.error("Failed parsing.")
        return ReturnCode.PARSE_ERR

    # ----------------------------------
    # Type check
    # ----------------------------------
    (well_typed, context) = type_check(
        program, 
        str_to_r2u2_implementation(impl), 
        mission_time,
        enable_atomic_checkers, 
        enable_booleanizer,
        enable_assemble,
        signal_mapping
    )

    if not well_typed:
        logger.error("Failed type check.")
        return ReturnCode.TYPE_CHECK_ERR

    # ----------------------------------
    # Transforms
    # ----------------------------------
    for transform in [t for t in TRANSFORM_PIPELINE if t in enabled_transforms]:
        transform(program, context)

    if dump_ast:
        ast_bytes = program.dumps()
        with open(input_path.with_suffix(".pickle"), "wb") as f:
            f.write(ast_bytes)

    if not enable_assemble:
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Assembly
    # ----------------------------------
    binary = assemble(program, context, quiet)
    with open(output_filename, "wb") as f:
        f.write(binary)

    return ReturnCode.SUCCESS

