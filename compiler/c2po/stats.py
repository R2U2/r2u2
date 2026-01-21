from dataclasses import dataclass

@dataclass
class Stats:
    """
    A class to store statistics for the compiler.
    """
    spec_filename: str = ""
    total_scq_size: int = 0

    smt_encoding_time: float = 0.0
    smt_solver_time: float = 0.0
    smt_solver_result: str = "none"
    smt_num_calls: int = 0

    eqsat_encoding_time: float = 0.0
    eqsat_solver_time: float = 0.0
    eqsat_solver_status: str = "ok"

    eqsat_gurobi_encoding_time: float = 0.0
    eqsat_gurobi_solver_time: float = 0.0
    eqsat_gurobi_solver_status: str = "ok"

    eqsat_equiv_result: str = "none"
    eqsat_equiv_encoding_time: float = 0.0
    eqsat_equiv_solver_time: float = 0.0

    def set_spec_filename(self, filename: str) -> None:
        """Sets the specification filename of the statistics."""
        self.spec_filename = filename

    def reset_smt_stats(self) -> None:
        """Resets the SMT statistics."""
        self.smt_encoding_time = 0.0
        self.smt_solver_time = 0.0
        self.smt_solver_result = "none"
        self.smt_num_calls = 0

    def format(self, format_str: str) -> str:
        """Formats the statistics according to the given format string.
        The format string can contain the following placeholders and escape sequences:
        - \n = Newline
        - %F = Input Filename
        - %S = Total SCQ size
        - %sr = SMT solver result
        - %se = SMT encoding time
        - %st = SMT solver time
        - %sn = SMT solver number of calls
        - %en = Eqsat encoding time
        - %et = Eqsat solver time
        - %es = Eqsat solver status
        - %ge = Eqsat Gurobi encoding time
        - %gt = Eqsat Gurobi solver time
        - %gs = Eqsat Gurobi solver result
        - %eq = Eqsat equivalence result
        - %ee = Eqsat equivalence solver time
        - %ed = Eqsat equivalence encoding time
        """
        format_str = format_str.replace("%F", str(self.spec_filename))
        format_str = format_str.replace("%S", str(self.total_scq_size))
        format_str = format_str.replace("%se", str(self.smt_encoding_time))
        format_str = format_str.replace("%st", str(self.smt_solver_time))
        format_str = format_str.replace("%sr", self.smt_solver_result)
        format_str = format_str.replace("%sn", str(self.smt_num_calls))
        format_str = format_str.replace("%en", str(self.eqsat_encoding_time))
        format_str = format_str.replace("%et", str(self.eqsat_solver_time))
        format_str = format_str.replace("%es", self.eqsat_solver_status)
        format_str = format_str.replace("%ge", str(self.eqsat_gurobi_encoding_time))
        format_str = format_str.replace("%gt", str(self.eqsat_gurobi_solver_time))
        format_str = format_str.replace("%gs", self.eqsat_gurobi_solver_status)
        format_str = format_str.replace("%eq", self.eqsat_equiv_result)
        format_str = format_str.replace("%ee", str(self.eqsat_equiv_solver_time))
        format_str = format_str.replace("%ed", str(self.eqsat_equiv_encoding_time))
        format_str = format_str.replace("\\n", "\n")
        format_str = format_str.replace("\\\"", "\"")
        return format_str

    def deepcopy(self) -> "Stats":
        return Stats(
            spec_filename=self.spec_filename,
            total_scq_size=self.total_scq_size,
            smt_encoding_time=self.smt_encoding_time,
            smt_solver_time=self.smt_solver_time,
            smt_solver_result=self.smt_solver_result,
            smt_num_calls=self.smt_num_calls,
            eqsat_encoding_time=self.eqsat_encoding_time,
            eqsat_solver_time=self.eqsat_solver_time,
            eqsat_equiv_result=self.eqsat_equiv_result,
            eqsat_equiv_encoding_time=self.eqsat_equiv_encoding_time,
            eqsat_equiv_solver_time=self.eqsat_equiv_solver_time,
        )
