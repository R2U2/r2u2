from dataclasses import dataclass

@dataclass
class Stats:
    """
    A class to store statistics for the compiler.
    """
    total_scq_size: int = 0

    smt_encoding_time: float = 0.0
    smt_solver_time: float = 0.0
    smt_solver_result: str = "none"
    smt_num_calls: int = 0

    eqsat_encoding_time: float = 0.0
    eqsat_solver_time: float = 0.0
    eqsat_equiv_result: str = "none"
    eqsat_equiv_encoding_time: float = 0.0
    eqsat_equiv_solver_time: float = 0.0

    def reset_smt_stats(self) -> None:
        """Resets the SMT statistics."""
        self.smt_encoding_time = 0.0
        self.smt_solver_time = 0.0
        self.smt_solver_result = "none"
        self.smt_num_calls = 0

    def print(self, format_str: str) -> None:
        """Prints the statistics in the according to the given format string.
        The format string can contain the following placeholders:
        - %S = Total SCQ size
        - %sr = SMT solver result
        - %se = SMT encoding time
        - %st = SMT solver time
        - %sn = SMT solver number of calls
        - %ee = Eqsat encoding time
        - %et = Eqsat solver time
        - %eq = Eqsat equivalence result
        - %eq = Eqsat equivalence time
        - %es = Eqsat equivalence solver time
        - %ed = Eqsat equivalence encoding time
        """
        format_str = format_str.replace("%S", str(self.total_scq_size))
        format_str = format_str.replace("%se", str(self.smt_encoding_time))
        format_str = format_str.replace("%st", str(self.smt_solver_time))
        format_str = format_str.replace("%sr", self.smt_solver_result)
        format_str = format_str.replace("%sn", str(self.smt_num_calls))
        format_str = format_str.replace("%ee", str(self.eqsat_encoding_time))
        format_str = format_str.replace("%et", str(self.eqsat_solver_time))
        format_str = format_str.replace("%eq", self.eqsat_equiv_result)
        format_str = format_str.replace("%es", str(self.eqsat_equiv_encoding_time))
        format_str = format_str.replace("%ed", str(self.eqsat_equiv_solver_time))
        print(format_str)
