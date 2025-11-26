from __future__ import annotations

import enum
import pathlib
import pickle
import tempfile
import shutil
from typing import Optional

from c2po import (
    assemble,
    cpt,
    log,
    parse_c2po,
    parse_mltl,
    parse_equiv,
    type_check,
    passes,
    serialize,
    options,
    sat
)

MODULE_CODE = "MAIN"


class ReturnCode(enum.Enum):
    SUCCESS = 0
    ERROR = 1
    PARSE_ERR = 2
    TYPE_CHECK_ERR = 3
    ASM_ERR = 4
    INVALID_INPUT = 5
    FILE_IO_ERR = 6


def wrap_up(program: cpt.Program, context: cpt.Context) -> None:
    """Wrap up the program, including cleanup and finalization."""
    log.debug(MODULE_CODE, 1, "Cleaning up")
    serialize.write_outputs(program, context)
    if context.options.copyback_enabled:
        shutil.copytree(context.options.workdir, context.options.copyback_path)
    if context.options.stats_format_str:
        context.stats.print(context.options.stats_format_str)
    log.debug(MODULE_CODE, 1, "Done")


def compile(opts: options.Options) -> ReturnCode:
    """Compile a C2PO input file, output generated R2U2 binaries and return error/success code.

    Compilation stages:
    2. Parse
    3. Type check
    3a. Equivalence check (if input is an equivalence specification)
    4. Required passes
    5. Option-based passes
    6. Optimizations
    7. Assembly
    """
    # ----------------------------------
    # Parse
    # ----------------------------------
    bounds: list[cpt.SymbolicIntervalVariable] = []
    constraints: list[cpt.Expression] = []
    if opts.spec_format == options.SpecFormat.C2PO:
        program: Optional[cpt.Program] = parse_c2po.parse_c2po(
            opts.spec_path, opts.mission_time
        )

        if not program:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

    elif opts.spec_format == options.SpecFormat.MLTL:
        parse_output = parse_mltl.parse_mltl(opts.spec_path, opts.mission_time)

        if not parse_output:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

        (program, signal_mapping) = parse_output
        opts.signal_mapping = signal_mapping
    elif opts.spec_format == options.SpecFormat.PICKLE:
        with open(str(opts.spec_path), "rb") as f:
            program = pickle.load(f)

        if not isinstance(program, cpt.Program):
            log.error(MODULE_CODE, "Bad pickle file")
            return ReturnCode.PARSE_ERR
    elif opts.spec_format == options.SpecFormat.EQUIV:
        equiv_parse_output = parse_equiv.parse_equiv(opts.spec_path)

        if not equiv_parse_output:
            log.error(MODULE_CODE, "Failed parsing")
            return ReturnCode.PARSE_ERR

        (program, bounds, constraints) = equiv_parse_output

        # Equivalence checking requires booleanizer expressions, so we enable it here so that the
        # type checker can pass
        opts.enable_booleanizer = True
        opts.assembly_enabled = False
        opts.smt_encoding = options.SMTTheories.UFLIA_INF # Equivalence checking requires UFLIA_INF encoding
    else:
        return ReturnCode.INVALID_INPUT

    if opts.only_parse:
        return ReturnCode.SUCCESS
    
    # ----------------------------------
    # Type check
    # ----------------------------------
    (well_typed, context) = type_check.type_check(program, opts)

    if not well_typed:
        log.error(MODULE_CODE, "Failed type check")
        return ReturnCode.TYPE_CHECK_ERR

    if opts.only_type_check:
        wrap_up(program, context)
        return ReturnCode.SUCCESS

    if opts.spec_format == options.SpecFormat.EQUIV:
        # Then we just do the equivalence check and return
        sat_result = sat.check_equiv(program, bounds, constraints, context)
        if sat_result is sat.SatResult.SAT:
            log.error(MODULE_CODE, "Equivalence check failed")
            return ReturnCode.ERROR
        elif sat_result is sat.SatResult.UNSAT:
            return ReturnCode.SUCCESS
        elif sat_result is sat.SatResult.TIMEOUT:
            log.error(MODULE_CODE, "Equivalence check timed out")
            return ReturnCode.ERROR
        elif sat_result is sat.SatResult.UNKNOWN:
            log.error(MODULE_CODE, "Equivalence check unknown")
            return ReturnCode.ERROR
        elif sat_result is sat.SatResult.MEMOUT:
            log.error(MODULE_CODE, "Equivalence check memory out")
            return ReturnCode.ERROR
        elif sat_result is sat.SatResult.FAILURE:
            log.error(MODULE_CODE, "Equivalence check internal failure")
            return ReturnCode.ERROR

    # ----------------------------------
    # Transforms
    # ----------------------------------
    log.debug(MODULE_CODE, 1, "Performing passes")
    for cpass in passes.pass_list:
        cpass(program, context)
        if not context.status:
            return ReturnCode.ERROR

    if opts.only_compile:
        wrap_up(program, context)
        return ReturnCode.SUCCESS

    # ----------------------------------
    # Assembly
    # ----------------------------------
    if not opts.output_path:
        log.error(MODULE_CODE, f"Output path invalid: {opts.output_path}")
        if opts.copyback_enabled:
            shutil.copytree(opts.workdir, opts.copyback_path)
        return ReturnCode.INVALID_INPUT

    (assembly, binary) = assemble.assemble(program, context)

    if not opts.quiet:
        [print(instr) for instr in assembly]

    with open(opts.output_path, "wb") as f:
        f.write(binary)

    wrap_up(program, context)
    return ReturnCode.SUCCESS


def main(opts: options.Options) -> ReturnCode:
    status = opts.setup()
    passes.setup(opts)
    if not status:
        return ReturnCode.ERROR

    with tempfile.TemporaryDirectory() as workdir:
        workdir_path = pathlib.Path(workdir)
        opts.workdir = workdir_path
        return compile(opts)


def main_rs(
    spec_filename: str,
    trace_filename: str,
    map_filename: str,
    output_filename: str,
    enable_aux: bool,
    enable_booleanizer: bool,
    enable_rewrite: bool,
    enable_cse: bool,
    enable_sat: bool,
    timeout_sat: int
):
    """Wrapper for main function to allow for easier interfacing with Rust CLI tool and playground."""
    opts = options.Options(
        spec_filename=spec_filename,
        trace_filename=trace_filename if trace_filename != "" else None,
        map_filename=map_filename if map_filename != "" else None,
        output_filename=output_filename,
        enable_aux=enable_aux,
        enable_booleanizer=enable_booleanizer,
        enable_rewrite=enable_rewrite,
        enable_cse=enable_cse,
        enable_sat=enable_sat,
        smt_max_time=timeout_sat,
    )
    return main(opts)
