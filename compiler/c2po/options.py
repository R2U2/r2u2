import pathlib
import enum
from typing import Optional

from c2po import types, log, passes, parse

MODULE_CODE = "OPTS"

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

class Options:
    workdir: pathlib.Path
    spec_filename: str = ""
    spec_path: pathlib.Path
    trace_filename: str = ""
    map_filename: str = ""
    signal_mapping: types.SignalMapping
    output_filename: str = "spec.bin"
    output_path: pathlib.Path
    impl: str = "c"
    implementation: types.R2U2Implementation
    mission_time: int = -1
    int_width: int = 8
    int_is_signed: bool = False
    float_width: int = 32
    endian: str = "@"
    frontend: types.R2U2Engine
    only_parse: bool = False
    only_type_check: bool = False
    only_compile: bool = False
    assembly_enabled: bool
    enabled_passes: set
    enable_atomic_checkers: bool = False
    enable_booleanizer: bool = False
    enable_extops: bool = False
    enable_nnf: bool = False
    enable_bnf: bool = False
    enable_rewrite: bool = False
    enable_eqsat: bool = False
    enable_cse: bool = False
    enable_sat: bool = False
    write_c2po_filename: str = "."
    write_prefix_filename: str = "."
    write_mltl_filename: str = "."
    write_pickle_filename: str = "."
    write_smt_dir: str = "."
    timeout_eqsat: int = 3600
    timeout_sat: int = 3600
    timeout_egglog: int = 3600
    copyback_name: Optional[str] = None
    copyback_path: Optional[pathlib.Path]
    stats: bool = False
    debug: bool = False
    log_level: int = 0
    quiet: bool = False

    def validate(self) -> bool:
        """Validate the input options/files. Checks for option compatibility, file existence, and sets certain options."""
        if self.debug:
            log.set_log_level(5)
        else:
            log.set_log_level(self.log_level)

        if self.stats:
            log.set_report_stats()

        log.debug(MODULE_CODE, 1, "Validating input")
        status: bool = True

        self.input_path = pathlib.Path(self.spec_filename)
        if not self.input_path.is_file():
            log.error(MODULE_CODE, f"Input file '{self.spec_filename} not a valid file.'")
            status = False

        if self.trace_filename != "":
            self.trace_path = pathlib.Path(self.trace_filename)
            if not self.trace_path.is_file():
                log.error(MODULE_CODE, f"Trace file '{self.trace_filename}' is not a valid file")
                status = False

        if self.map_filename != "":
            self.map_path = pathlib.Path(self.map_filename)
            if not self.map_path.is_file():
                log.error(MODULE_CODE, f"Map file '{self.map_filename}' is not a valid file")
                status = False

        self.output_path = pathlib.Path(self.output_filename)

        if self.copyback_name:
            self.copyback_path = pathlib.Path(self.copyback_name)
            if self.copyback_path.exists():
                log.error(MODULE_CODE, f"Directory already exists '{self.copyback_path}'")
                status = False

        signal_mapping: Optional[types.SignalMapping] = None
        trace_length = -1

        if self.trace_path:
            (trace_length, signal_mapping) = parse.parse_trace_file(
                self.trace_path, self.map_path is not None
            )
        if self.map_path:
            signal_mapping = parse.parse_map_file(self.map_path)

        if not signal_mapping:
            signal_mapping = {}

        if self.mission_time > -1:
            # warn if the given trace is shorter than the defined mission time
            if trace_length > -1 and trace_length < self.mission_time:
                log.warning(
                    MODULE_CODE,
                    f"Trace length is shorter than given mission time ({trace_length} < {self.mission_time})",
                )
        else:
            self.mission_time = trace_length

        if self.endian in BYTE_ORDER_SIGILS:
            self.endian_sigil = BYTE_ORDER_SIGILS[self.endian]
        else:
            log.internal(
                MODULE_CODE,
                f"Endianness option argument {self.endian} invalid. Check CLI options?",
            )
            self.endian_sigil = "@"

        impl = R2U2_IMPL_MAP[self.impl]
        types.configure_types(impl, self.int_width, self.int_is_signed, self.float_width)

        if impl in {types.R2U2Implementation.CPP, types.R2U2Implementation.VHDL}:
            if self.enable_extops:
                log.error(
                    MODULE_CODE, "Extended operators only support for C implementation"
                )
                status = False

        if self.enable_nnf and self.enable_bnf:
            log.warning(
                MODULE_CODE, "Attempting rewrite to both NNF and BNF, defaulting to NNF"
            )

        if not self.enable_extops and (self.enable_nnf or self.enable_bnf):
            log.warning(
                MODULE_CODE,
                "NNF and BNF incompatible without extended operators, output will not be in either normal form",
            )

        self.enabled_passes = set(passes.PASS_LIST)
        if not self.enable_rewrite:
            self.enabled_passes.remove(passes.optimize_rewrite_rules)

        if not self.enable_cse:
            self.enabled_passes.remove(passes.optimize_cse)

        if self.enable_extops:
            self.enabled_passes.remove(passes.remove_extended_operators)

        if self.enable_eqsat:
            if passes.optimize_rewrite_rules in self.enabled_passes:
                self.enabled_passes.remove(passes.optimize_rewrite_rules)
            if passes.optimize_cse in self.enabled_passes:
                self.enabled_passes.remove(passes.optimize_cse)
            if passes.remove_extended_operators in self.enabled_passes:
                self.enabled_passes.remove(passes.remove_extended_operators)

            # since optimize_egraph flattens operators, no need to convert them to binary
            self.enabled_passes.remove(passes.multi_operators_to_binary)
        else: # not enable_egraph
            self.enabled_passes.remove(passes.optimize_eqsat)
            
        if not self.enable_nnf:
            self.enabled_passes.remove(passes.to_nnf)

        if not self.enable_bnf:
            self.enabled_passes.remove(passes.to_bnf)

        if not self.enable_sat:
            self.enabled_passes.remove(passes.check_sat)

        if self.only_parse:
            self.final_stage = CompilationStage.PARSE
        elif self.only_type_check:
            self.final_stage = CompilationStage.TYPE_CHECK
        elif self.only_compile:
            self.final_stage = CompilationStage.PASSES
        else:
            self.final_stage = CompilationStage.ASSEMBLE

        if self.enable_booleanizer and self.enable_atomic_checkers:
            log.error(MODULE_CODE, "Only one of atomic checkers and booleanizer can be enabled")
            status = False
        elif self.enable_booleanizer and impl != types.R2U2Implementation.C:
            log.error(MODULE_CODE, "Booleanizer only available for C implementation")
            status = False

        if self.enable_booleanizer:
            self.frontend = types.R2U2Engine.BOOLEANIZER
        elif self.enable_atomic_checkers:
            self.frontend = types.R2U2Engine.ATOMIC_CHECKER
        else:
            self.frontend = types.R2U2Engine.NONE

        return status
