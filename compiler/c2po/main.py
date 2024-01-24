from __future__ import annotations
from typing import Optional, NamedTuple
import logging
import re
from enum import Enum
from pathlib import Path

from c2po import log
from c2po import types
from c2po import cpt
from c2po import parse
from c2po import type_check
from c2po import transform
from c2po import assemble


class ReturnCode(Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_INPUT = 5
    FILE_IO_ERR = 6


class ValidatedInput(NamedTuple):
    status: bool
    input_path: Optional[Path]
    output_path: Optional[Path]
    mission_time: int
    endian_sigil: str
    signal_mapping: types.SignalMapping
    transforms: set[transform.C2POTransform]


# Converts human names to struct format sigil for byte order, used by assembler
# human named args are called 'endian' while the sigils are 'endianness'
# See: https://docs.python.org/3.8/library/struct.html#byte-order-size-and-alignment
BYTE_ORDER_SIGILS = {"native": "@", "network": "!", "big": ">", "little": "<"}


def process_trace_file(
    trace_path: Path, map_file_provided: bool
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
            log.logger.warning(
                "Map file given and header included in trace file; header will be ignored."
            )

        for id in [s.strip() for s in header.split(",")]:
            if id in signal_mapping:
                log.logger.warning(
                    f"{trace_path.name}:{1}: Signal ID '{id}' found multiple times in csv, using right-most value."
                )
            signal_mapping[id] = cnt
            cnt += 1

        trace_length = len(lines) - 1

        return (trace_length, signal_mapping)

    # no header, so just return number of lines in file (i.e., number of time steps in trace)
    return (len(lines), None)


def process_map_file(map_path: Path) -> Optional[types.SignalMapping]:
    """Given `trace_path`, return the inferred mission time and, if `return_mapping` is enabled, a signal mapping."""
    with open(map_path, "r") as f:
        content: str = f.read()

    mapping: types.SignalMapping = {}

    lines = content.splitlines()
    for line in lines:
        if re.match("[a-zA-Z_]\\w*:\\d+", line):
            strs = line.split(":")
            id = strs[0]
            sid = int(strs[1])

            if id in mapping:
                log.logger.warning(
                    f"{map_path.name}:{lines.index(line)+1}: Signal ID '{id}' found multiple times in map file, using latest value."
                )

            mapping[id] = sid
        else:
            log.logger.error(
                f"{map_path.name}:{lines.index(line)}: Invalid format for map line (found {line})\n\t Should be of the form SYMBOL ':' NUMERAL"
            )
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
    endian: str,
    enable_atomic_checkers: bool = False,
    enable_booleanizer: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_rewrite: bool = False,
    enable_arity: bool = False,
    enable_cse: bool = False,
    enable_assemble: bool = True,
) -> ValidatedInput:
    """Validate the input options/files. Checks for option compatibility, file existence, and sets certain options.

    Returns:
        A tuple with the following item types/descriptions:
        `bool`: validation status
        `Optional[Path]`: path corresponding to `input_filename` if it is a valid file, `None` otherwise
        `Optional[Path]`: path corresponding to `output_filename` if it is a valid file, `None` otherwise
        `int`: mission time, either set to `custom_mission_time` or the input trace length if not provided
        `str`: endianness string from `BYTE_ORDER_SIGILS`
        `Optional[types.SignalMapping]`: signal mapping if it was derived from `trace_filename` or `map_filebame`, `None` otherwise
        `set[C2POTransform]`: set of transforms to apply to the input
    """
    status: bool = True

    input_path = Path(input_filename)
    if not input_path.is_file():
        log.logger.error(f" Input file '{input_filename} not a valid file.'")
        input_path = None

    trace_path = None
    if trace_filename != "":
        trace_path = Path(trace_filename)
        if not trace_path.is_file():
            log.logger.error(f" Trace file '{trace_filename}' is not a valid file.")

    map_path = None
    if map_filename != "":
        map_path = Path(map_filename)
        if not map_path.is_file():
            log.logger.error(f" Map file '{map_filename}' is not a valid file.")

    output_path = None
    if output_filename != "":
        output_path = Path(output_filename)
        if output_path.is_file():
            log.logger.warning(f" Output file '{output_filename}' already exists.")

    signal_mapping: Optional[types.SignalMapping] = None
    mission_time, trace_length = -1, -1

    if trace_path:
        (trace_length, signal_mapping) = process_trace_file(
            trace_path, map_path is not None
        )
    if map_path:
        signal_mapping = process_map_file(map_path)

    if not signal_mapping:
        signal_mapping = {}

    if custom_mission_time > -1:
        mission_time = custom_mission_time

        # warn if the given trace is shorter than the defined mission time
        if trace_length > -1 and trace_length < custom_mission_time:
            log.logger.warning(
                f" Trace length is shorter than given mission time ({trace_length} < {custom_mission_time})."
            )
    else:
        mission_time = trace_length

    if endian in BYTE_ORDER_SIGILS:
        endian_sigil = BYTE_ORDER_SIGILS[endian]
    else:
        log.logger.critical(
            f" Endianness option argument {endian} invalid. Check CLI options?"
        )
        endian_sigil = "@"

    impl: types.R2U2Implementation = types.str_to_r2u2_implementation(impl_str)
    types.set_types(impl, int_width, int_is_signed, float_width)

    if enable_booleanizer and enable_atomic_checkers:
        log.logger.error(" Only one of AT and booleanizer can be enabled")
        status = False

    if impl == types.R2U2Implementation.C:
        if (not enable_booleanizer and not enable_atomic_checkers) or (
            enable_booleanizer and enable_atomic_checkers
        ):
            log.logger.error(
                " Exactly one of booleanizer or atomic checker must be enabled for C implementation."
            )
            status = False
    else:  # impl == R2U2Implementation.CPP or impl == R2U2Implementation.VHDL
        if enable_booleanizer:
            log.logger.error(" Booleanizer only available for C implementation.")
            status = False

    if impl in {types.R2U2Implementation.CPP, types.R2U2Implementation.VHDL}:
        if enable_extops:
            log.logger.error(" Extended operators only support for C implementation.")
            status = False

    if enable_nnf and enable_bnf:
        log.logger.warning(
            " Attempting rewrite to both NNF and BNF, defaulting to NNF."
        )

    transforms = set(transform.TRANSFORM_PIPELINE)
    if not enable_rewrite:
        transforms.remove(transform.optimize_rewrite_rules)
    if enable_extops:
        transforms.remove(transform.transform_extended_operators)
    if not enable_nnf:
        transforms.remove(transform.transform_negative_normal_form)
    if not enable_bnf:
        transforms.remove(transform.transform_boolean_normal_form)
    if not enable_cse:
        transforms.remove(transform.optimize_cse)

    return ValidatedInput(
        status,
        input_path,
        output_path,
        mission_time,
        endian_sigil,
        signal_mapping,
        transforms,
    )


def dump(
    program: cpt.Program,
    input_path: Path,
    dump_ast_filename: str,
    dump_mltl_std_filename: str,
) -> None:
    """Dumps pickled AST and AST in MLTL standard format if filenames are not '.'"""
    if dump_ast_filename != ".":
        dump_path = (
            Path(dump_ast_filename)
            if dump_ast_filename != ""
            else input_path.with_suffix(".pickle").name
        )
        ast_bytes = program.pickle()
        with open(dump_path, "wb") as f:
            f.write(ast_bytes)

    if dump_mltl_std_filename != ".":
        dump_path = (
            Path(dump_mltl_std_filename)
            if dump_mltl_std_filename != ""
            else input_path.with_suffix(".mltl").name
        )
        with open(dump_path, "w") as f:
            f.write(program.to_mltl_std())


def compile(
    input_filename: str,
    trace_filename: str = "",
    map_filename: str = "",
    output_filename: str = "spec.bin",
    impl: str = "c",
    custom_mission_time: Optional[int] = None,
    int_width: int = 8,
    int_signed: bool = False,
    float_width: int = 32,
    endian: str = "@",
    enable_atomic_checkers: bool = False,
    enable_booleanizer: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_rewrite: bool = False,
    enable_arity: bool = False,
    enable_cse: bool = False,
    enable_assemble: bool = True,
    dump_ast_filename: str = ".",
    dump_mltl_std_filename: str = ".",
    debug: bool = False,
    quiet: bool = False,
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
        input_filename: Name of a C2PO or MLTL file -- uses extension to determine file type
        trace_filename:
        map_filename:
        output_filename: Name of binary output file
        impl: An R2U2 implementation to target. Should be one of `c`, `c++`, `cpp`, `fpga`, or `vhdl`
        int_width: Width to set C2POIntType to. Should be one of 8, 16, 32, or 64
        mission_time: Value of mission-time to replace `M` with in specs
        int_signed: If true sets C2POIntType to signed
        float_width: Width to set C2POFloatType to. Should be one of 32 or 64
        endianness:
        enable_atomic_checkers: If true enables Atomic Checker instructions
        enable_booleanizer: If true enables Booleanizer instructions
        enable_extops: If true enables TL extended operators (or, implies, future, release)
        enable_nnf: If true enables negation normal form of MLTL
        enable_bnf: If true enables boolean normal form of MLTL
        enable_rewrite: If true enables MLTL rewrite rule optimizations
        enable_arity: If true enables operator arity optimization
        enable_cse: If true enables Common Subexpression Elimination
        enable_assemble: If true outputs binary to output_filename
        dump_ast_filename:
        dump_mltl_std_filename:
        debug:
        quiet: If true disables assembly output to stdout
    """
    if debug:
        log.logger.setLevel(logging.DEBUG)

    # ----------------------------------
    # Input validation
    # ----------------------------------
    options = validate_input(
        input_filename,
        trace_filename,
        map_filename,
        output_filename,
        impl,
        custom_mission_time if custom_mission_time else -1,
        int_width,
        int_signed,
        float_width,
        endian,
        enable_atomic_checkers,
        enable_booleanizer,
        enable_extops,
        enable_nnf,
        enable_bnf,
        enable_rewrite,
        enable_arity,
        enable_cse,
        enable_assemble,
    )

    if not options.status or not options.input_path:
        log.logger.error(" Input invalid.")
        return ReturnCode.INVALID_INPUT

    # ----------------------------------
    # Parse
    # ----------------------------------
    if options.input_path.suffix == ".c2po":
        program: Optional[cpt.Program] = parse.parse_c2po(
            options.input_path, options.mission_time
        )

        if not program:
            log.logger.error(" Failed parsing.")
            return ReturnCode.PARSE_ERR

        # must have defined this in trace or map file
        signal_mapping = options.signal_mapping

    else:  # we treat as an MLTL file
        parse_output = parse.parse_mltl(options.input_path, options.mission_time)

        if not parse_output:
            log.logger.error(" Failed parsing.")
            return ReturnCode.PARSE_ERR

        (program, signal_mapping) = parse_output

    # ----------------------------------
    # Type check
    # ----------------------------------
    (well_typed, context) = type_check.type_check(
        program,
        types.str_to_r2u2_implementation(impl),
        options.mission_time,
        enable_atomic_checkers,
        enable_booleanizer,
        enable_assemble,
        signal_mapping,
    )

    if not well_typed:
        log.logger.error(" Failed type check.")
        return ReturnCode.TYPE_CHECK_ERR

    # ----------------------------------
    # Transforms
    # ----------------------------------
    for trans in [t for t in transform.TRANSFORM_PIPELINE if t in options.transforms]:
        trans(program, context)

    # Optional file dumps
    dump(program, options.input_path, dump_ast_filename, dump_mltl_std_filename)

    if not enable_assemble:
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Assembly
    # ----------------------------------
    if not options.output_path:
        log.logger.error(" Input invalid.")
        return ReturnCode.INVALID_INPUT

    binary = assemble.assemble(program, context, quiet, options.endian_sigil)
    with open(options.output_path, "wb") as f:
        f.write(binary)

    return ReturnCode.SUCCESS
