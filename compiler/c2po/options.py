from dataclasses import dataclass, field
import pathlib
import enum

from c2po import types, log, parse

MODULE_CODE = "OPTS"

EMPTY_FILENAME = ""

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

@dataclass
class Options:
    spec_filename: str
    trace_filename: str
    map_filename: str
    output_filename: str
    impl_str: str
    mission_time: int
    int_width: int
    int_is_signed: bool
    float_width: int
    only_parse: bool
    only_type_check: bool
    only_compile: bool
    enable_aux: bool
    enable_booleanizer: bool
    enable_extops: bool
    enable_nnf: bool
    enable_bnf: bool
    enable_rewrite: bool
    enable_eqsat: bool
    enable_cse: bool
    enable_sat: bool
    timeout_eqsat: int
    timeout_sat: int
    write_c2po_filename: str
    write_prefix_filename: str
    write_mltl_filename: str
    write_pickle_filename: str
    write_smt_dirname: str
    copyback_dirname: str
    stats: bool
    debug: bool
    log_level: int
    quiet: bool

    workdir: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
    spec_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
    output_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
    signal_mapping: types.SignalMapping = field(default_factory=dict)

    impl: types.R2U2Implementation = types.R2U2Implementation.C
    frontend: types.R2U2Engine = types.R2U2Engine.NONE
    final_stage: CompilationStage = CompilationStage.ASSEMBLE
    assembly_enabled: bool = True
    enabled_passes: set = field(default_factory=set)
    smt_solver: str = "z3"
    write_c2po: bool = False
    write_prefix: bool = False
    write_mltl: bool = False
    write_pickle: bool = False
    write_smt: bool = False
    copyback_enabled: bool = False
    copyback_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)

    def setup(self) -> bool:
        """Validate the input options/files. Checks for option compatibility, file existence, and sets certain options. 
        **Must call `passes.setup()` after this function.**"""
        if self.debug:
            log.set_log_level(5)
        else:
            log.set_log_level(self.log_level)

        if self.stats:
            log.set_report_stats()

        log.debug(MODULE_CODE, 1, "Validating input")
        status: bool = True

        self.spec_path = pathlib.Path(self.spec_filename)
        if not self.spec_path.is_file():
            log.error(MODULE_CODE, f"Input file '{self.spec_filename} not a valid file.'")
            status = False
        
        self.trace_path = None
        if self.trace_filename is not None:
            self.trace_path = pathlib.Path(self.trace_filename)
            if not self.trace_path.is_file():
                log.error(MODULE_CODE, f"Trace file '{self.trace_filename}' is not a valid file")
                status = False

        self.map_path = None
        if self.map_filename is not None:
            self.map_path = pathlib.Path(self.map_filename)
            if not self.map_path.is_file():
                log.error(MODULE_CODE, f"Map file '{self.map_filename}' is not a valid file")
                status = False

        self.output_path = pathlib.Path(self.output_filename)

        if self.copyback_enabled:
            self.copyback_path = pathlib.Path(self.copyback_dirname)
            if self.copyback_path.exists():
                log.error(MODULE_CODE, f"Directory already exists '{self.copyback_path}'")
                status = False

        tmp_signal_mapping = None
        self.trace_length = -1

        if self.trace_path:
            (self.trace_length, tmp_signal_mapping) = parse.parse_trace_file(
                self.trace_path, self.map_path is not None
            )
        if self.map_path:
            tmp_signal_mapping = parse.parse_map_file(self.map_path)

        if not tmp_signal_mapping:
            self.signal_mapping = {}
        else:
            self.signal_mapping = tmp_signal_mapping

        if self.mission_time > -1:
            # warn if the given trace is shorter than the defined mission time
            if self.trace_length > -1 and self.trace_length < self.mission_time:
                log.warning(
                    MODULE_CODE,
                    f"Trace length is shorter than given mission time ({self.trace_length} < {self.mission_time})",
                )
        else:
            self.ission_time = self.trace_length

        self.impl = R2U2_IMPL_MAP[self.impl_str]
        types.configure_types(self.impl, self.int_width, self.int_is_signed, self.float_width)

        if self.impl in {types.R2U2Implementation.CPP, types.R2U2Implementation.VHDL}:
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

        if self.only_parse:
            final_stage = CompilationStage.PARSE
        elif self.only_type_check:
            final_stage = CompilationStage.TYPE_CHECK
        elif self.only_compile:
            final_stage = CompilationStage.PASSES
        else:
            final_stage = CompilationStage.ASSEMBLE

        self.assembly_enabled = (final_stage == CompilationStage.ASSEMBLE)

        if self.enable_booleanizer and self.impl != types.R2U2Implementation.C:
            log.error(MODULE_CODE, "Booleanizer only available for C implementation")
            status = False

        if self.enable_booleanizer:
            self.frontend = types.R2U2Engine.BOOLEANIZER
        else:
            self.frontend = types.R2U2Engine.NONE

        if self.write_c2po_filename == EMPTY_FILENAME:
            self.write_c2po_filename = f"{self.spec_path.stem}.c2po"
        if self.write_prefix_filename == EMPTY_FILENAME:
            self.write_prefix_filename = f"{self.spec_path.stem}.c2po.prefix"
        if self.write_mltl_filename == EMPTY_FILENAME:
            self.write_mltl_filename = f"{self.spec_path.stem}.mltl"
        if self.write_pickle_filename == EMPTY_FILENAME:
            self.write_pickle_filename = f"{self.spec_path.stem}.pickle"
        if self.write_smt_dirname == EMPTY_FILENAME:
            self.write_smt_dirname = f"{self.spec_path.stem}_smt"

        return status
