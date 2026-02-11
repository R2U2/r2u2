from dataclasses import dataclass

STATS_FORMAT_MAP: dict[str, str] = {
    "F": "spec_filename",
    "scq": "total_scq_size",
    "satres": "smt_solver_result",
    "satenc": "smt_encoding_time",
    "sattime": "smt_solver_time",
    "satnc": "smt_num_calls",
    "eqsatenc": "eqsat_encoding_time",
    "eqsattime": "eqsat_solver_time",
    "eqsatstatus": "eqsat_solver_status",
    "eqsateclasses": "eqsat_num_eclasses",
    "eqsatenodes": "eqsat_num_enodes",
    "eqsatgurenc": "eqsat_gurobi_encoding_time",
    "eqsatgurtime": "eqsat_gurobi_solver_time",
    "eqsatgurstatus": "eqsat_gurobi_solver_status",
    "eqsateqres": "eqsat_equiv_result",
    "eqsateqtime": "eqsat_equiv_solver_time",
    "eqsateqenc": "eqsat_equiv_encoding_time",
    "r2u2median": "r2u2_median_runtime",
    "r2u2average": "r2u2_average_runtime",
    "r2u2min": "r2u2_min_runtime",
    "r2u2max": "r2u2_max_runtime",
    "r2u2status": "r2u2_status",
}

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

    eqsat_num_eclasses: int = 0
    eqsat_num_enodes: int = 0

    eqsat_gurobi_encoding_time: float = 0.0
    eqsat_gurobi_solver_time: float = 0.0
    eqsat_gurobi_solver_status: str = "ok"

    eqsat_equiv_result: str = "none"
    eqsat_equiv_encoding_time: float = 0.0
    eqsat_equiv_solver_time: float = 0.0

    r2u2_median_runtime: float = 0.0
    r2u2_average_runtime: float = 0.0
    r2u2_min_runtime: float = 0.0
    r2u2_max_runtime: float = 0.0
    r2u2_status: str = "ok"

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
        """Formats the statistics according to the format string.
        """
        for key, value in STATS_FORMAT_MAP.items():
            format_str = format_str.replace(f"%{key}", str(getattr(self, value)))
        format_str = format_str.replace("\\n", "\n")
        format_str = format_str.replace("\\\"", "\"")
        format_str = format_str.replace("\\t", "\t")
        return format_str

    def get_help_message(self) -> str:
        """Returns the help message for the statistics."""
        return (
            "The format string can contain the following placeholders and escape sequences:\n"
            + "\n".join([f"- %{key}: {value}" for key, value in STATS_FORMAT_MAP.items()])
            + "\nEscape sequences:\n"
            + "- \\n = Newline\n"
            + "- \\\" = Double quote\n"
            + "- \\t = Tab"
        )

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
