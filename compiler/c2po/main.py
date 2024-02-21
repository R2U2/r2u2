from __future__ import annotations

import enum
import pathlib
import re
import pickle
from typing import Optional

from c2po import assemble, cpt, log, parse, type_check, types, passes, serialize, util

MODULE_CODE = "MAIN"


class ReturnCode(enum.Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_INPUT = 5
    FILE_IO_ERR = 6


# Converts human names to struct format sigil for byte order, used by assembler
# human named args are called 'endian' while the sigils are 'endianness'
# See: https://docs.python.org/3.8/library/struct.html#byte-order-size-and-alignment
BYTE_ORDER_SIGILS = {"native": "@", "network": "!", "big": ">", "little": "<"}

R2U2_IMPL_MAP = {
    "c": types.R2U2Implementation.C,
    "cpp": types.R2U2Implementation.CPP,
    "vhdl": types.R2U2Implementation.VHDL,
}


def process_trace_file(
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


def process_map_file(map_path: pathlib.Path) -> Optional[types.SignalMapping]:
    """Return the signal mapping from `map_path`."""
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


def validate_input(
    input_filename: str,
    trace_filename: str,
    map_filename: str,
    output_filename: str,
    workdir: str,
    impl_str: str,
    custom_mission_time: int,
    int_width: int,
    int_is_signed: bool,
    float_width: int,
    endian: str,
    only_parse: bool = False,
    only_type_check: bool = False,
    only_compile: bool = False,
    enable_atomic_checkers: bool = False,
    enable_booleanizer: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_rewrite: bool = False,
    enable_egraph: bool = False,
    enable_cse: bool = False,
    enable_sat: bool = False,
) -> Optional[tuple[cpt.Config, set[passes.Pass]]]:
    """Validate the input options/files. Checks for option compatibility, file existence, and sets certain options."""
    log.debug(MODULE_CODE, 1, "Validating input")
    status: bool = True

    input_path = pathlib.Path(input_filename)
    if not input_path.is_file():
        log.error(MODULE_CODE, f"Input file '{input_filename} not a valid file.'")
        status = False

    trace_path = None
    if trace_filename != "":
        trace_path = pathlib.Path(trace_filename)
        if not trace_path.is_file():
            log.error(MODULE_CODE, f"Trace file '{trace_filename}' is not a valid file")

    map_path = None
    if map_filename != "":
        map_path = pathlib.Path(map_filename)
        if not map_path.is_file():
            log.error(MODULE_CODE, f"Map file '{map_filename}' is not a valid file")

    output_path = pathlib.Path(output_filename)

    if not workdir or workdir == "":
        workdir_path = util.DEFAULT_WORKDIR
    else:
        workdir_parent = pathlib.Path(workdir) 

        if not workdir_parent.exists():
            log.warning(MODULE_CODE, f"workdir parent path {workdir_parent} does not exist, defaulting to {util.DEFAULT_WORKDIR}")
            workdir_path = util.DEFAULT_WORKDIR
        else:
            workdir_path = pathlib.Path(workdir) / util.DEFAULT_WORKDIR_NAME

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
            log.warning(
                MODULE_CODE,
                f"Trace length is shorter than given mission time ({trace_length} < {custom_mission_time})",
            )
    else:
        mission_time = trace_length

    if endian in BYTE_ORDER_SIGILS:
        endian_sigil = BYTE_ORDER_SIGILS[endian]
    else:
        log.internal(
            MODULE_CODE,
            f"Endianness option argument {endian} invalid. Check CLI options?",
        )
        endian_sigil = "@"

    impl = R2U2_IMPL_MAP[impl_str]
    types.set_types(impl, int_width, int_is_signed, float_width)

    if impl in {types.R2U2Implementation.CPP, types.R2U2Implementation.VHDL}:
        if enable_extops:
            log.error(
                MODULE_CODE, "Extended operators only support for C implementation"
            )
            status = False

    if enable_nnf and enable_bnf:
        log.warning(
            MODULE_CODE, "Attempting rewrite to both NNF and BNF, defaulting to NNF"
        )

    if not enable_extops and (enable_nnf or enable_bnf):
        log.warning(
            MODULE_CODE,
            "NNF and BNF incompatible without extended operators, output will not be in either normal form",
        )

    enabled_passes = set(passes.PASS_LIST)
    if not enable_rewrite:
        enabled_passes.remove(passes.optimize_rewrite_rules)

    if not enable_cse:
        enabled_passes.remove(passes.optimize_cse)

    if enable_extops:
        enabled_passes.remove(passes.remove_extended_operators)

    if enable_egraph:
        if passes.optimize_rewrite_rules in enabled_passes:
            enabled_passes.remove(passes.optimize_rewrite_rules)
        if passes.optimize_cse in enabled_passes:
            enabled_passes.remove(passes.optimize_cse)
        if passes.remove_extended_operators in enabled_passes:
            enabled_passes.remove(passes.remove_extended_operators)

        # since optimize_egraph flattens operators, no need to convert them to binary
        enabled_passes.remove(passes.multi_operators_to_binary)
    else: # not enable_egraph
        enabled_passes.remove(passes.optimize_egraph)
        
    if not enable_nnf:
        enabled_passes.remove(passes.to_nnf)

    if not enable_bnf:
        enabled_passes.remove(passes.to_bnf)

    if not enable_sat:
        enabled_passes.remove(passes.check_sat)

    if only_parse:
        final_stage = cpt.CompilationStage.PARSE
    elif only_type_check:
        final_stage = cpt.CompilationStage.TYPE_CHECK
    elif only_compile:
        final_stage = cpt.CompilationStage.PASSES
    else:
        final_stage = cpt.CompilationStage.ASSEMBLE

    if enable_booleanizer and enable_atomic_checkers:
        log.error(MODULE_CODE, "Only one of atomic checkers and booleanizer can be enabled")
        status = False
    elif enable_booleanizer and impl != types.R2U2Implementation.C:
        log.error(MODULE_CODE, "Booleanizer only available for C implementation")
        status = False

    if enable_booleanizer:
        frontend = types.R2U2Engine.BOOLEANIZER
    elif enable_atomic_checkers:
        frontend = types.R2U2Engine.ATOMIC_CHECKER
    else:
        frontend = types.R2U2Engine.NONE

    if not status:
        return None

    config = cpt.Config(
        input_path,
        output_path,
        workdir_path,
        impl,
        mission_time,
        endian_sigil,
        frontend,
        final_stage is cpt.CompilationStage.ASSEMBLE,
        signal_mapping,
    )

    return (config, enabled_passes)


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
    only_parse: bool = False,
    only_type_check: bool = False,
    only_compile: bool = False,
    enable_atomic_checkers: bool = False,
    enable_booleanizer: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_rewrite: bool = False,
    enable_egraph: bool = False,
    enable_cse: bool = False,
    enable_sat: bool = False,
    write_c2po_filename: str = ".",
    write_prefix_filename: str = ".",
    write_mltl_filename: str = ".",
    write_pickle_filename: str = ".",
    write_smt_dir: str = ".",
    keep: bool = False,
    workdir: str = "",
    stats: bool = False,
    debug: int = 0,
    quiet: bool = False,
) -> ReturnCode:
    """Compile a C2PO input file, output generated R2U2 binaries and return error/success code.

    Compilation stages:
    1. Input validation
    2. Parser
    3. Type checker
    4. Required passes
    5. Option-based passes
    6. Optimizations
    7. Assembly
    """
    if debug:
        log.set_debug(debug)

    if stats:
        log.set_stat()

    # ----------------------------------
    # Input validation
    # ----------------------------------
    validated_input = validate_input(
        input_filename,
        trace_filename,
        map_filename,
        output_filename,
        workdir,
        impl,
        custom_mission_time if custom_mission_time else -1,
        int_width,
        int_signed,
        float_width,
        endian,
        only_parse,
        only_type_check,
        only_compile,
        enable_atomic_checkers,
        enable_booleanizer,
        enable_extops,
        enable_nnf,
        enable_bnf,
        enable_rewrite,
        enable_egraph,
        enable_cse,
        enable_sat,
    )

    if not validated_input:
        log.error(MODULE_CODE, "Input invalid")
        return ReturnCode.INVALID_INPUT
    
    config, enabled_passes = validated_input

    # ----------------------------------
    # Parse
    # ----------------------------------
    if config.input_path.suffix == ".c2po":
        program: Optional[cpt.Program] = parse.parse_c2po(
            config.input_path, config.mission_time
        )

        if not program:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

    elif config.input_path.suffix == ".mltl":
        parse_output = parse.parse_mltl(config.input_path, config.mission_time)

        if not parse_output:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

        (program, signal_mapping) = parse_output
        config.signal_mapping = signal_mapping
    elif config.input_path.suffix == ".pickle":
        with open(str(config.input_path), "rb") as f:
            program = pickle.load(f)

        if not isinstance(program, cpt.Program):
            log.error(MODULE_CODE, "Bad pickle file")
            return ReturnCode.PARSE_ERR
    else:
        log.error(
            MODULE_CODE, f"Unsupported input format ({config.input_path.suffix})"
        )
        return ReturnCode.INVALID_INPUT

    if only_parse:
        serialize.write_outputs(
            program,
            cpt.Context.Empty(),
            config.input_path,
            write_c2po_filename,
            write_prefix_filename,
            write_mltl_filename,
            write_pickle_filename,
            write_smt_dir,
        )
        return ReturnCode.SUCCESS
    
    # ----------------------------------
    # Type check
    # ----------------------------------
    (well_typed, context) = type_check.type_check(program, config)

    if not well_typed:
        log.error(MODULE_CODE, "Failed type check")
        return ReturnCode.TYPE_CHECK_ERR

    if only_type_check:
        serialize.write_outputs(
            program,
            context,
            config.input_path,
            write_c2po_filename,
            write_prefix_filename,
            write_mltl_filename,
            write_pickle_filename,
            write_smt_dir,
        )
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Transforms
    # ----------------------------------
    util.setup_dir(config.workdir)

    log.debug(MODULE_CODE, 1, "Performing passes")
    for cpass in [t for t in passes.PASS_LIST if t in enabled_passes]:
        cpass(program, context)

    if only_compile:
        serialize.write_outputs(
            program,
            context,
            config.input_path,
            write_c2po_filename,
            write_prefix_filename,
            write_mltl_filename,
            write_pickle_filename,
            write_smt_dir,
        )
        if not keep:
            util.cleanup_dir(config.workdir)
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Assembly
    # ----------------------------------
    if not config.output_path:
        log.error(MODULE_CODE, f"Output path invalid: {config.output_path}")
        if not keep:
            util.cleanup_dir(config.workdir)
        return ReturnCode.INVALID_INPUT

    (assembly, binary) = assemble.assemble(
        program, context, quiet, config.endian_sigil
    )

    if not quiet:
        [print(instr) for instr in assembly]

    with open(config.output_path, "wb") as f:
        f.write(binary)

    serialize.write_outputs(
        program,
        context,
        config.input_path,
        write_c2po_filename,
        write_prefix_filename,
        write_mltl_filename,
        write_pickle_filename,
        write_smt_dir,
    )

    if not keep:
        util.cleanup_dir(config.workdir)

    return ReturnCode.SUCCESS
