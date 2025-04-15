from dataclasses import dataclass, field
from typing import Optional
import pathlib
import enum
import resource

from c2po import types, log, parse_utils

MODULE_CODE = "OPTS"

EMPTY_FILENAME = ""

R2U2_IMPL_MAP = {
    "c": types.R2U2Implementation.C,
    "cpp": types.R2U2Implementation.CPP,
    "vhdl": types.R2U2Implementation.VHDL,
    "rust": types.R2U2Implementation.RUST,
}

class SpecFormat(enum.Enum):
    C2PO = ".c2po"
    MLTL = ".mltl"
    PICKLE = ".pickle"

class SMTTheories(enum.Enum):
    UFLIA = "uflia"
    QF_UFLIA = "qf_uflia"
    AUFLIA = "auflia"
    QF_AUFLIA = "qf_auflia"
    AUFBV = "aufbv"
    QF_AUFBV = "qf_aufbv"
    QF_BV = "qf_bv"
    QF_BV_INCR = "qf_bv_incr"
    QF_BV_LOG = "qf_bv_log"
    QF_BV_LOG_INCR = "qf_bv_log_incr"

class CompilationStage(enum.Enum):
    PARSE = 0
    TYPE_CHECK = 1
    PASSES = 2
    ASSEMBLE = 3

DEFAULTS = {
    "trace_filename": None,
    "map_filename": None,
    "output_filename": "spec.bin",
    "impl_str": "c",
    "mission_time": -1,
    "int_width": 32,
    "int_is_signed": False,
    "float_width": 32,
    "only_parse": False,
    "only_type_check": False,
    "only_compile": False,
    "enable_aux": True,
    "enable_booleanizer": False,
    "enable_extops": False,
    "enable_nnf": False,
    "enable_bnf": False,
    "enable_rewrite": True,
    "enable_eqsat": False,
    "enable_cse": True,
    "enable_sat": False,
    "write_bounds_filename": None,
    "egglog": "egglog",
    "eqsat_max_time": 3600,
    "eqsat_max_memory": 0,
    "smt_solver": "z3",
    "smt_options": [],
    "smt_encoding_str": "uflia",
    "smt_max_time": 3600,
    "smt_max_memory": 0,
    "write_c2po_filename": None,
    "write_prefix_filename": None,
    "write_mltl_filename": None,
    "write_pickle_filename": None,
    "write_smt_dirname": None,
    "copyback_dirname": None,
    "stats": False,
    "debug": False,
    "log_level": 0,
    "quiet": False,
}

@dataclass
class Options:
    spec_filename: str
    trace_filename: Optional[str] = DEFAULTS["trace_filename"]
    map_filename: Optional[str] = DEFAULTS["map_filename"]
    output_filename: str = DEFAULTS["output_filename"]
    impl_str: str = DEFAULTS["impl_str"]
    mission_time: int = DEFAULTS["mission_time"]
    int_width: int = DEFAULTS["int_width"]
    int_is_signed: bool = DEFAULTS["int_is_signed"]
    float_width: int = DEFAULTS["float_width"]
    only_parse: bool = DEFAULTS["only_parse"]
    only_type_check: bool = DEFAULTS["only_type_check"]
    only_compile: bool = DEFAULTS["only_compile"]
    enable_aux: bool = DEFAULTS["enable_aux"]
    enable_booleanizer: bool = DEFAULTS["enable_booleanizer"]
    enable_extops: bool = DEFAULTS["enable_extops"]
    enable_nnf: bool = DEFAULTS["enable_nnf"]
    enable_bnf: bool = DEFAULTS["enable_bnf"]
    enable_rewrite: bool = DEFAULTS["enable_rewrite"]
    enable_eqsat: bool = DEFAULTS["enable_eqsat"]
    enable_cse: bool = DEFAULTS["enable_cse"]
    enable_sat: bool = DEFAULTS["enable_sat"]
    write_bounds_filename: Optional[str] = DEFAULTS["write_bounds_filename"]
    egglog: str = DEFAULTS["egglog"]
    eqsat_max_time: int = DEFAULTS["eqsat_max_time"]
    eqsat_max_memory: int = DEFAULTS["eqsat_max_memory"]
    smt_solver: str = DEFAULTS["smt_solver"]
    smt_options: list[str] = field(default_factory=list)
    smt_encoding_str: str = DEFAULTS["smt_encoding_str"]
    smt_max_time: int = DEFAULTS["smt_max_time"]
    smt_max_memory: int = DEFAULTS["smt_max_memory"]
    write_c2po_filename: Optional[str] = DEFAULTS["write_c2po_filename"]
    write_prefix_filename: Optional[str] = DEFAULTS["write_prefix_filename"]
    write_mltl_filename: Optional[str] = DEFAULTS["write_mltl_filename"]
    write_pickle_filename: Optional[str] = DEFAULTS["write_pickle_filename"]
    write_smt_dirname: Optional[str] = DEFAULTS["write_smt_dirname"]
    copyback_dirname: Optional[str] = DEFAULTS["copyback_dirname"]
    stats: bool = DEFAULTS["stats"]
    debug: bool = DEFAULTS["debug"]
    log_level: int = DEFAULTS["log_level"]
    quiet: bool = DEFAULTS["quiet"]

    spec_format: SpecFormat = SpecFormat.C2PO
    workdir: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
    spec_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
    output_path: pathlib.Path = pathlib.Path(EMPTY_FILENAME)
    signal_mapping: types.SignalMapping = field(default_factory=dict)
    impl: types.R2U2Implementation = types.R2U2Implementation.C
    frontend: types.R2U2Engine = types.R2U2Engine.NONE
    final_stage: CompilationStage = CompilationStage.ASSEMBLE
    assembly_enabled: bool = True
    enabled_passes: set = field(default_factory=set)
    smt_encoding: SMTTheories = SMTTheories.UFLIA
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

        if self.spec_path.suffix == SpecFormat.C2PO.value:
            self.spec_format = SpecFormat.C2PO
        elif self.spec_path.suffix == SpecFormat.MLTL.value:
            self.spec_format = SpecFormat.MLTL
        elif self.spec_path.suffix == SpecFormat.PICKLE.value:
            self.spec_format = SpecFormat.PICKLE
        else:
            log.error(MODULE_CODE, f"Input file '{self.spec_filename}' has an invalid format.")
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

        if self.copyback_dirname is not None:
            self.copyback_path = pathlib.Path(self.copyback_dirname)
            if self.copyback_path.exists():
                log.error(MODULE_CODE, f"Directory already exists '{self.copyback_path}'")
                status = False
            self.copyback_enabled = True

        tmp_signal_mapping = None
        self.trace_length = -1

        if self.trace_path:
            (self.trace_length, tmp_signal_mapping) = parse_utils.parse_trace_file(
                self.trace_path, self.map_path is not None
            )
        if self.map_path:
            tmp_signal_mapping = parse_utils.parse_map_file(self.map_path)

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
            self.mission_time = self.trace_length

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

        if self.eqsat_max_memory == 0:
            self.eqsat_max_memory = resource.RLIM_INFINITY
        else:
            self.eqsat_max_memory = self.eqsat_max_memory * 1024 * 1024

        if self.smt_max_memory == 0:
            self.smt_max_memory = resource.RLIM_INFINITY
        else:
            self.smt_max_memory = self.smt_max_memory * 1024 * 1024
            
        if self.smt_encoding_str == "uflia":
            self.smt_encoding = SMTTheories.UFLIA
        elif self.smt_encoding_str == "qf_uflia":
            self.smt_encoding = SMTTheories.QF_UFLIA
        elif self.smt_encoding_str == "auflia":
            self.smt_encoding = SMTTheories.AUFLIA
        elif self.smt_encoding_str == "qf_auflia":
            self.smt_encoding = SMTTheories.QF_AUFLIA
        elif self.smt_encoding_str == "aufbv":
            self.smt_encoding = SMTTheories.AUFBV
        elif self.smt_encoding_str == "qf_aufbv":
            self.smt_encoding = SMTTheories.QF_AUFBV
        elif self.smt_encoding_str == "qf_bv":
            self.smt_encoding = SMTTheories.QF_BV
        elif self.smt_encoding_str == "qf_bv_incr":
            self.smt_encoding = SMTTheories.QF_BV_INCR
        elif self.smt_encoding_str == "qf_bv_log":
            self.smt_encoding = SMTTheories.QF_BV_LOG
        elif self.smt_encoding_str == "qf_bv_log_incr":
            self.smt_encoding = SMTTheories.QF_BV_LOG_INCR
        else:
            log.error(MODULE_CODE, f"Invalid SMT theory '{self.smt_encoding_str}'")
            status = False

        return status
