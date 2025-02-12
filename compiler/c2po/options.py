import pathlib
import enum

from c2po import types, log, parse

MODULE_CODE = "OPTS"

EMPTY_FILENAME = ""

# Converts human names to struct format sigil for byte order, used by assembler
# human named args are called 'endian' while the sigils are 'endianness'
# See: https://docs.python.org/3.8/library/struct.html#byte-order-size-and-alignment
BYTE_ORDER_SIGILS = {"native": "@", "network": "!", "big": ">", "little": "<"}

R2U2_IMPL_MAP = {
    "c": types.R2U2Implementation.C,
    "cpp": types.R2U2Implementation.CPP,
    "vhdl": types.R2U2Implementation.VHDL,
}

class CompilationStage(enum.Enum):
    PARSE = 0
    TYPE_CHECK = 1
    PASSES = 2
    ASSEMBLE = 3

spec_filename: str = EMPTY_FILENAME
trace_filename: str = EMPTY_FILENAME
map_filename: str = EMPTY_FILENAME
output_filename: str = "spec.bin"

workdir: pathlib.Path = pathlib.Path(EMPTY_FILENAME)

spec_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
output_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)

signal_mapping: types.SignalMapping = {}
impl_str: str = "c"
impl: types.R2U2Implementation = types.R2U2Implementation.C
mission_time: int = -1
int_width: int = 8
int_is_signed: bool = False
float_width: int = 32
endian: str = "native"
endian_sigil: str = "@"

frontend: types.R2U2Engine = types.R2U2Engine.NONE

only_parse: bool = False
only_type_check: bool = False
only_compile: bool = False
final_stage: CompilationStage = CompilationStage.ASSEMBLE

assembly_enabled: bool = True

enabled_passes: set = set()
enable_atomic_checkers: bool = False
enable_booleanizer: bool = False
enable_extops: bool = False
enable_nnf: bool = False
enable_bnf: bool = False
enable_rewrite: bool = False
enable_eqsat: bool = False
enable_cse: bool = False
enable_sat: bool = False

smt_solver: str = "z3"
timeout_eqsat: int = 3600
timeout_sat: int = 3600

write_c2po: bool = False
write_prefix: bool = False
write_mltl: bool = False
write_pickle: bool = False
write_smt: bool = False
write_c2po_filename: str = EMPTY_FILENAME
write_prefix_filename: str = EMPTY_FILENAME
write_mltl_filename: str = EMPTY_FILENAME
write_pickle_filename: str = EMPTY_FILENAME
write_smt_dirname: str = EMPTY_FILENAME

copyback_enabled: bool = False
copyback_dirname: str = EMPTY_FILENAME
copyback_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)

stats: bool = False
debug: bool = False
log_level: int = 0
quiet: bool = False


def setup() -> bool:
    """Validate the input options/files. Checks for option compatibility, file existence, and sets certain options. 
    **Must call `passes.setup()` after this function.**"""
    global spec_filename, trace_filename, map_filename, output_filename, \
        spec_path, output_path, \
        signal_mapping, impl, mission_time, int_width, int_is_signed, float_width, endian, endian_sigil, \
        frontend, only_parse, only_type_check, only_compile, final_stage, assembly_enabled, \
        enable_atomic_checkers, enable_booleanizer, enable_extops, enable_nnf, enable_bnf, enable_rewrite, enable_eqsat, enable_cse, enable_sat, \
        smt_solver, timeout_eqsat, timeout_sat, \
        copyback_enabled, copyback_dirname, copyback_path, \
        write_c2po, write_prefix, write_mltl, write_pickle, write_smt, \
        write_c2po_filename, write_prefix_filename, write_mltl_filename, write_pickle_filename, write_smt_dirname, \
        stats, debug, log_level, quiet 

    if debug:
        log.set_log_level(5)
    else:
        log.set_log_level(log_level)

    if stats:
        log.set_report_stats()

    log.debug(MODULE_CODE, 1, "Validating input")
    status: bool = True

    spec_path = pathlib.Path(spec_filename)
    if not spec_path.is_file():
        log.error(MODULE_CODE, f"Input file '{spec_filename} not a valid file.'")
        status = False
    
    trace_path = None
    if trace_filename != EMPTY_FILENAME:
        trace_path = pathlib.Path(trace_filename)
        if not trace_path.is_file():
            log.error(MODULE_CODE, f"Trace file '{trace_filename}' is not a valid file")
            status = False

    map_path = None
    if map_filename != EMPTY_FILENAME:
        map_path = pathlib.Path(map_filename)
        if not map_path.is_file():
            log.error(MODULE_CODE, f"Map file '{map_filename}' is not a valid file")
            status = False

    output_path = pathlib.Path(output_filename)

    if copyback_enabled:
        copyback_path = pathlib.Path(copyback_dirname)
        if copyback_path.exists():
            log.error(MODULE_CODE, f"Directory already exists '{copyback_path}'")
            status = False

    tmp_signal_mapping = None
    trace_length = -1

    if trace_path:
        (trace_length, tmp_signal_mapping) = parse.parse_trace_file(
            trace_path, map_path is not None
        )
    if map_path:
        tmp_signal_mapping = parse.parse_map_file(map_path)

    if not tmp_signal_mapping:
        signal_mapping = {}
    else:
        signal_mapping = tmp_signal_mapping

    if mission_time > -1:
        # warn if the given trace is shorter than the defined mission time
        if trace_length > -1 and trace_length < mission_time:
            log.warning(
                MODULE_CODE,
                f"Trace length is shorter than given mission time ({trace_length} < {mission_time})",
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
    types.configure_types(impl, int_width, int_is_signed, float_width)

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

    if only_parse:
        final_stage = CompilationStage.PARSE
    elif only_type_check:
        final_stage = CompilationStage.TYPE_CHECK
    elif only_compile:
        final_stage = CompilationStage.PASSES
    else:
        final_stage = CompilationStage.ASSEMBLE

    assembly_enabled = (final_stage == CompilationStage.ASSEMBLE)

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

    if write_c2po and write_c2po_filename == EMPTY_FILENAME:
        write_c2po_filename = f"{spec_path.stem}.c2po"
    if write_prefix and write_prefix_filename == EMPTY_FILENAME:
        write_prefix_filename = f"{spec_path.stem}.c2po.prefix"
    if write_mltl and write_mltl_filename == EMPTY_FILENAME:
        write_mltl_filename = f"{spec_path.stem}.mltl"
    if write_pickle and write_pickle_filename == EMPTY_FILENAME:
        write_pickle_filename = f"{spec_path.stem}.pickle"
    if write_smt and write_smt_dirname == EMPTY_FILENAME:
        write_smt_dirname = f"{spec_path.stem}_smt"

    return status
