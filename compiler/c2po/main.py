from __future__ import annotations

import enum
import pathlib
import pickle
import tempfile
import shutil
from typing import Optional

from c2po import assemble, cpt, log, parse, type_check, passes, serialize, options

MODULE_CODE = "MAIN"


class ReturnCode(enum.Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_INPUT = 5
    FILE_IO_ERR = 6


def compile(opts: options.Options) -> ReturnCode:
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
    # ----------------------------------
    # Input validation
    # ----------------------------------
    status = opts.validate()

    if not status:
        log.error(MODULE_CODE, "Input invalid")
        return ReturnCode.INVALID_INPUT

    # ----------------------------------
    # Parse
    # ----------------------------------
    if opts.input_path.suffix == ".c2po":
        program: Optional[cpt.Program] = parse.parse_c2po(
            opts.input_path, opts.mission_time
        )

        if not program:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

    elif opts.input_path.suffix == ".mltl":
        parse_output = parse.parse_mltl(opts.input_path, opts.mission_time)

        if not parse_output:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

        (program, signal_mapping) = parse_output
        opts.signal_mapping = signal_mapping
    elif opts.input_path.suffix == ".pickle":
        with open(str(opts.input_path), "rb") as f:
            program = pickle.load(f)

        if not isinstance(program, cpt.Program):
            log.error(MODULE_CODE, "Bad pickle file")
            return ReturnCode.PARSE_ERR
    else:
        log.error(
            MODULE_CODE, f"Unsupported input format ({opts.input_path.suffix})"
        )
        return ReturnCode.INVALID_INPUT

    if opts.only_parse:
        serialize.write_outputs(
            program,
            cpt.Context(),
            opts.input_path,
            opts.write_c2po_filename,
            opts.write_prefix_filename,
            opts.write_mltl_filename,
            opts.write_pickle_filename,
            opts.write_smt_dir,
        )
        return ReturnCode.SUCCESS
    
    # ----------------------------------
    # Type check
    # ----------------------------------
    (well_typed, context) = type_check.type_check(program, opts)

    if not well_typed:
        log.error(MODULE_CODE, "Failed type check")
        return ReturnCode.TYPE_CHECK_ERR

    if opts.only_type_check:
        serialize.write_outputs(
            program,
            context,
            opts.input_path,
            opts.write_c2po_filename,
            opts.write_prefix_filename,
            opts.write_mltl_filename,
            opts.write_pickle_filename,
            opts.write_smt_dir,
        )
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Transforms
    # ----------------------------------
    log.debug(MODULE_CODE, 1, "Performing passes")
    for cpass in [t for t in passes.PASS_LIST if t in opts.enabled_passes]:
        cpass(program, context)
        if not context.status:
            return ReturnCode.ERROR

    if opts.only_compile:
        serialize.write_outputs(
            program,
            context,
            opts.input_path,
            opts.write_c2po_filename,
            opts.write_prefix_filename,
            opts.write_mltl_filename,
            opts.write_pickle_filename,
            opts.write_smt_dir,
        )
        if opts.copyback_path:
            shutil.copytree(opts.workdir, opts.copyback_path)
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Assembly
    # ----------------------------------
    if not opts.output_path:
        log.error(MODULE_CODE, f"Output path invalid: {opts.output_path}")
        if opts.copyback_path:
            shutil.copytree(opts.workdir, opts.copyback_path)
        return ReturnCode.INVALID_INPUT

    (assembly, binary) = assemble.assemble(
        program, context, opts.quiet, opts.endian_sigil
    )

    if not opts.quiet:
        [print(instr) for instr in assembly]

    with open(opts.output_path, "wb") as f:
        f.write(binary)

    serialize.write_outputs(
        program,
        context,
        opts.input_path,
        opts.write_c2po_filename,
        opts.write_prefix_filename,
        opts.write_mltl_filename,
        opts.write_pickle_filename,
        opts.write_smt_dir,
    )

    if opts.copyback_path:
        shutil.copytree(opts.workdir, opts.copyback_path)

    return ReturnCode.SUCCESS



def main(
    spec_filename: str,
    trace_filename: str = "",
    map_filename: str = "",
    output_filename: str = "spec.bin",
    impl: str = "c",
    mission_time: int = -1,
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
    enable_eqsat: bool = False,
    enable_cse: bool = False,
    enable_sat: bool = False,
    write_c2po_filename: str = ".",
    write_prefix_filename: str = ".",
    write_mltl_filename: str = ".",
    write_pickle_filename: str = ".",
    write_smt_dir: str = ".",
    timeout_eqsat: int = 3600,
    timeout_sat: int = 3600,
    copyback_name: Optional[str] = None,
    stats: bool = False,
    debug: bool = False,
    log_level: int = 0,
    quiet: bool = False,
) -> ReturnCode:
    """Wrapper around `compile` for creating a global temporary directory as a working directory and setting Options."""
    opts = options.Options()
    opts.spec_filename = spec_filename
    opts.trace_filename = trace_filename
    opts.map_filename = map_filename
    opts.output_filename = output_filename
    opts.impl = impl
    opts.mission_time = mission_time
    opts.int_width = int_width
    opts.int_is_signed = int_signed
    opts.float_width = float_width
    opts.endian = endian
    opts.only_parse = only_parse
    opts.only_type_check = only_type_check
    opts.only_compile = only_compile
    opts.enable_atomic_checkers = enable_atomic_checkers
    opts.enable_booleanizer = enable_booleanizer
    opts.enable_extops = enable_extops
    opts.enable_nnf = enable_nnf
    opts.enable_bnf = enable_bnf
    opts.enable_rewrite = enable_rewrite
    opts.enable_eqsat = enable_eqsat
    opts.enable_cse = enable_cse
    opts.enable_sat = enable_sat
    opts.write_c2po_filename = write_c2po_filename
    opts.write_prefix_filename = write_prefix_filename
    opts.write_mltl_filename = write_mltl_filename
    opts.write_pickle_filename = write_pickle_filename
    opts.write_smt_dir = write_smt_dir
    opts.timeout_eqsat = timeout_eqsat
    opts.timeout_sat = timeout_sat
    opts.copyback_name = copyback_name
    opts.stats = stats
    opts.debug = debug
    opts.log_level = log_level
    opts.quiet = quiet

    with tempfile.TemporaryDirectory() as workdir:
        workdir_path = pathlib.Path(workdir)
        opts.workdir = workdir_path
        return compile(opts)

