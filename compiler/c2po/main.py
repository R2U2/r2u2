from __future__ import annotations

import enum
import pathlib
import pickle
import tempfile
import shutil
from typing import Optional

from c2po import assemble, cpt, log, parse, type_check, passes, serialize, options, first_order

MODULE_CODE = "MAIN"


class ReturnCode(enum.Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_INPUT = 5
    FILE_IO_ERR = 6


def compile() -> ReturnCode:
    """Compile a C2PO input file, output generated R2U2 binaries and return error/success code.

    Compilation stages:
    1. Input validation
    2. Parser
    3. Type checker
    4. Required passes
    5. Option-based passes
    6. Optimizations
    7. Assembly

    There is a special 'first-order' mode that is enabled by the --first-order flag.
    """
    if options.enable_first_order:
        log.debug(MODULE_CODE, 1, f"Compiling first-order formula ({options.fo_bounds_path})")
        parsed = first_order.parse_fo(options.spec_path, options.fo_bounds_path, options.mission_time)
        if not parsed:
            log.error(MODULE_CODE, "Failed parsing first-order formula")
            return ReturnCode.PARSE_ERR
        (expr, bounds) = parsed
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Parse
    # ----------------------------------
    if options.spec_path.suffix == ".c2po":
        program: Optional[cpt.Program] = parse.parse_c2po(
            options.spec_path, options.mission_time
        )

        if not program:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

    elif options.spec_path.suffix == ".mltl":
        parse_output = parse.parse_mltl(options.spec_path, options.mission_time)

        if not parse_output:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

        (program, signal_mapping) = parse_output
        options.signal_mapping = signal_mapping
    elif options.spec_path.suffix == ".pickle":
        with open(str(options.spec_path), "rb") as f:
            program = pickle.load(f)

        if not isinstance(program, cpt.Program):
            log.error(MODULE_CODE, "Bad pickle file")
            return ReturnCode.PARSE_ERR
    else:
        log.error(
            MODULE_CODE, f"Unsupported input format ({options.spec_path.suffix})"
        )
        return ReturnCode.INVALID_INPUT

    if options.only_parse:
        return ReturnCode.SUCCESS
    
    # ----------------------------------
    # Type check
    # ----------------------------------
    (well_typed, context) = type_check.type_check(program)

    if not well_typed:
        log.error(MODULE_CODE, "Failed type check")
        return ReturnCode.TYPE_CHECK_ERR

    if options.only_type_check:
        serialize.write_outputs(program, context)
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Transforms
    # ----------------------------------
    log.debug(MODULE_CODE, 1, "Performing passes")
    for cpass in passes.pass_list:
        cpass(program, context)
        if not context.status:
            return ReturnCode.ERROR

    if options.only_compile:
        serialize.write_outputs(program, context)
        if options.copyback_enabled:
            shutil.copytree(options.workdir, options.copyback_path)
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Assembly
    # ----------------------------------
    if not options.output_path:
        log.error(MODULE_CODE, f"Output path invalid: {options.output_path}")
        if options.copyback_enabled:
            shutil.copytree(options.workdir, options.copyback_path)
        return ReturnCode.INVALID_INPUT

    (assembly, binary) = assemble.assemble(program, context)

    if not options.quiet:
        [print(instr) for instr in assembly]

    with open(options.output_path, "wb") as f:
        f.write(binary)

    serialize.write_outputs(program, context)

    if options.copyback_enabled:
        shutil.copytree(options.workdir, options.copyback_path)

    return ReturnCode.SUCCESS


def main(
    spec_filename: str,
    trace_filename: Optional[str] = None,
    map_filename: Optional[str] = None,
    output_filename: str = "spec.bin",
    enable_booleanizer: bool = False,
    enable_aux: bool = True,
    enable_rewrite: bool = True,
    enable_cse: bool = True,
    enable_sat: bool = False,
    timeout_sat: int = 3600,
    impl: str = "c",
    mission_time: int = -1,
    int_width: int = 32,
    int_signed: bool = False,
    float_width: int = 32,
    only_parse: bool = False,
    only_type_check: bool = False,
    only_compile: bool = False,
    enable_extops: bool = False,
    enable_nnf: bool = False,
    enable_bnf: bool = False,
    enable_eqsat: bool = False,
    write_c2po_filename: Optional[str] = None,
    write_prefix_filename: Optional[str] = None,
    write_mltl_filename: Optional[str] = None,
    write_pickle_filename: Optional[str] = None,
    write_smt_dirname: Optional[str] = None,
    timeout_eqsat: int = 3600,
    copyback_dirname: Optional[str] = None,
    enable_first_order: bool = False,
    fo_bounds_filename: Optional[str] = None,
    fo_trace_filename: Optional[str] = None,
    stats: bool = False,
    debug: bool = False,
    log_level: int = 0,
    quiet: bool = False,
) -> ReturnCode:
    options.spec_filename = spec_filename
    options.trace_filename = trace_filename if trace_filename else options.EMPTY_FILENAME
    options.map_filename = map_filename if map_filename else options.EMPTY_FILENAME
    options.output_filename = output_filename

    options.impl_str = impl
    options.mission_time = mission_time
    options.int_width = int_width
    options.int_is_signed = int_signed
    options.float_width = float_width

    options.only_parse = only_parse
    options.only_type_check = only_type_check
    options.only_compile = only_compile

    options.enable_aux = enable_aux
    options.enable_booleanizer = enable_booleanizer
    options.enable_extops = enable_extops
    options.enable_nnf = enable_nnf
    options.enable_bnf = enable_bnf
    options.enable_rewrite = enable_rewrite
    options.enable_eqsat = enable_eqsat
    options.enable_cse = enable_cse
    options.enable_sat = enable_sat

    options.write_c2po = write_c2po_filename is not None
    options.write_prefix = write_prefix_filename is not None
    options.write_mltl = write_mltl_filename is not None
    options.write_pickle = write_pickle_filename is not None
    options.write_smt_dirname = write_smt_dirname is not None
    options.write_c2po_filename = write_c2po_filename
    options.write_prefix_filename = write_prefix_filename
    options.write_mltl_filename = write_mltl_filename
    options.write_pickle_filename = write_pickle_filename
    options.write_smt_dirname = write_smt_dirname

    options.timeout_eqsat = timeout_eqsat
    options.timeout_sat = timeout_sat

    options.copyback_enabled = copyback_dirname is not None
    options.copyback_dirname = copyback_dirname

    options.enable_first_order = enable_first_order
    options.fo_bounds_filename = fo_bounds_filename if fo_bounds_filename else options.EMPTY_FILENAME
    options.fo_trace_filename = fo_trace_filename if fo_trace_filename else options.EMPTY_FILENAME

    options.stats = stats
    options.debug = debug
    options.log_level = log_level
    options.quiet = quiet

    status = options.setup()
    passes.setup()
    if not status:
        return ReturnCode.ERROR

    with tempfile.TemporaryDirectory() as workdir:
        workdir_path = pathlib.Path(workdir)
        options.workdir = workdir_path
        return compile()

