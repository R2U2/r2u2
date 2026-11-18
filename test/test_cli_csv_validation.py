"""End-to-end fail-closed CSV parsing tests for the C reference CLI.

Build the debug C monitor with `make -C monitors/c debug` before running.
The compiler and monitor are both real subprocesses, not mocks.
"""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
MONITOR = ROOT / "monitors/c/build/r2u2_debug"
COMPILER = ROOT / "compiler/c2po.py"


class CSVInputValidationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not MONITOR.is_file():
            raise RuntimeError("Run `make -C monitors/c debug` before this test")
        cls.tmp = tempfile.TemporaryDirectory()
        tmp = Path(cls.tmp.name)
        cls.specs = {}
        preprocessed = subprocess.run(
            [os.environ.get("CC", "cc"), "-E", "-P", "-x", "c", "-"],
            input="#include <stdio.h>\nBUFSIZ\n", text=True,
            capture_output=True, check=True,
        )
        cls.c_bufsiz = int(preprocessed.stdout.splitlines()[-1])
        full_signals = ",".join(f"s{i}" for i in range(256))
        full_trace = "# " + full_signals + "\n" + ",".join(["0"] * 256) + "\n"
        for kind, source, booleanizer in (
            ("atomic", "INPUT\n    s: bool;\nFTSPEC\n    s;\n", False),
            ("numeric", "INPUT\n    s: int;\nFTSPEC\n    s > 0;\n", True),
            ("two_atomic", "INPUT\n    BOOST,COAST: bool;\nFTSPEC\n    COAST;\n", False),
            ("full_atomic", f"INPUT\n    {full_signals}: bool;\nFTSPEC\n    s255;\n", False),
            ("full_numeric", f"INPUT\n    {full_signals}: int;\nFTSPEC\n    s255 > 0;\n", True),
        ):
            spec = tmp / f"{kind}.c2po"
            trace = tmp / f"{kind}.csv"
            binary = tmp / f"{kind}.bin"
            spec.write_text(source)
            trace.write_text(
                full_trace if kind.startswith("full_")
                else "# BOOST,COAST\n0,1\n" if kind == "two_atomic"
                else "# s\n0\n"
            )
            command = [sys.executable, str(COMPILER), "--spec", str(spec),
                       "--trace", str(trace), "--output", str(binary)]
            if booleanizer:
                command.append("--booleanizer")
            compiled = subprocess.run(command, cwd=ROOT, text=True,
                                      capture_output=True, check=False)
            assert compiled.returncode == 0, compiled.stderr
            cls.specs[kind] = binary

    @classmethod
    def tearDownClass(cls):
        cls.tmp.cleanup()

    def run_monitor(self, kind: str, csv: str):
        env = {**os.environ,
               "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1",
               "UBSAN_OPTIONS": "halt_on_error=1"}
        return subprocess.run([str(MONITOR), str(self.specs[kind])],
                              input=csv, text=True, capture_output=True,
                              check=False, env=env)

    def assert_csv_rejected_safely(self, result):
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("Invalid CSV", result.stderr)
        self.assertNotIn("AddressSanitizer", result.stderr)
        self.assertNotIn("runtime error:", result.stderr)

    def test_atomic_column_257_is_rejected_before_write(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", ",".join(["0"] * 257) + "\n"))

    def test_numeric_column_257_is_rejected_before_write(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("numeric", ",".join(["0"] * 257) + "\n"))

    def test_column_256_is_within_array_capacity(self):
        for kind in ("atomic", "numeric"):
            with self.subTest(kind=kind):
                result = self.run_monitor("full_" + kind, ",".join(["0"] * 256) + "\n")
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "0:0,F")

    def test_timestamp_without_signal_is_rejected(self):
        self.assert_csv_rejected_safely(self.run_monitor("atomic", "@0\n"))

    def test_bare_timestamp_marker_is_rejected(self):
        self.assert_csv_rejected_safely(self.run_monitor("atomic", "@\n"))

    def test_invalid_timestamp_does_not_look_like_eof(self):
        result = self.run_monitor("atomic", "0\n@invalid\n0\n")
        self.assertEqual(result.stdout.strip(), "0:0,F")
        self.assert_csv_rejected_safely(result)

    def test_valid_timestamp_still_runs(self):
        result = self.run_monitor("atomic", "@0 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:0,F")

    def test_timestamp_with_suffix_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "@1garbage 0\n"))

    def test_negative_timestamp_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "@-1 0\n"))

    def test_timestamp_integer_overflow_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "@4294967296 0\n"))

    def test_timestamp_cannot_exceed_verdict_time_field(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "@2147483648 0\n"))

    def test_timestamp_max_verdict_time_is_valid(self):
        result = self.run_monitor("atomic", "@2147483647 0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:2147483647,F")

    def test_overlong_data_record_is_rejected_as_one_record(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "0" * 9000 + "\n"))

    def test_overlong_header_is_rejected_before_data(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "# " + "x" * 9000 + "\n0\n"))

    def test_complete_final_record_at_buffer_boundary_is_allowed(self):
        # A BUFSIZ-1-byte record is complete even if only its newline, or
        # EOF, remains outside the initial fgets buffer.
        for terminator in ("", "\n"):
            with self.subTest(terminator=repr(terminator)):
                result = self.run_monitor(
                    "atomic", "0" * (self.c_bufsiz - 1) + terminator,
                )
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout.strip(), "0:0,T")

    @unittest.skipUnless(sys.platform.startswith("linux"),
                         "requires Linux directory stream read semantics")
    def test_trace_read_failure_is_not_silent_end_of_trace(self):
        # On Linux fopen(directory, "r") succeeds but reading it fails.
        result = subprocess.run(
            [str(MONITOR), str(self.specs["atomic"]), self.tmp.name],
            text=True, capture_output=True, check=False,
            env={**os.environ, "ASAN_OPTIONS": "detect_leaks=0:halt_on_error=1",
                 "UBSAN_OPTIONS": "halt_on_error=1"},
        )
        self.assert_csv_rejected_safely(result)

    def test_boolean_zero_has_same_meaning_with_crlf(self):
        result = self.run_monitor("atomic", "0\r\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:0,F")

    def test_embedded_carriage_return_cannot_split_signal_columns(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("atomic", "0\r1\n"))

    def test_header_declared_two_columns_accepts_complete_rows(self):
        result = self.run_monitor("two_atomic", "# BOOST,COAST\n0,1\n0,0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:0,T\n0:1,F")

    def test_header_declared_missing_column_rejects_before_next_verdict(self):
        result = self.run_monitor("two_atomic", "# BOOST,COAST\n0,1\n0\n")
        self.assertEqual(result.stdout.strip(), "0:0,T")
        self.assert_csv_rejected_safely(result)

    def test_header_declared_trailing_empty_column_is_rejected(self):
        result = self.run_monitor("two_atomic", "# BOOST,COAST\n0,1\n0,\n")
        self.assertEqual(result.stdout.strip(), "0:0,T")
        self.assert_csv_rejected_safely(result)

    def test_header_declared_leading_empty_column_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("two_atomic", "# BOOST,COAST\n,1\n"))

    def test_header_declared_interior_empty_column_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("two_atomic", "# BOOST,COAST\n0,,1\n"))

    def test_header_declared_whitespace_only_column_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("two_atomic", "# BOOST,COAST\n0, \t\n"))

    def test_header_declared_extra_column_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("two_atomic", "# BOOST,COAST\n0,1,0\n"))

    def test_empty_header_column_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("two_atomic", "# BOOST,\n0,1\n"))

    def test_whitespace_only_header_column_is_rejected(self):
        self.assert_csv_rejected_safely(
            self.run_monitor("two_atomic", "# BOOST, \t\n0,1\n"))

    def test_header_declaring_more_than_capacity_is_rejected(self):
        header = "# " + ",".join(f"s{i}" for i in range(257))
        self.assert_csv_rejected_safely(
            self.run_monitor("full_atomic", header + "\n0\n"))

    def test_header_declared_timestamped_rows_are_accepted(self):
        result = self.run_monitor("two_atomic", "# BOOST,COAST\n@0 0,1\n@1 0,0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:0,T\n0:1,F")

    def test_header_declared_crlf_rows_are_accepted(self):
        result = self.run_monitor("two_atomic", "# BOOST,COAST\r\n0,1\r\n0,0\r\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:0,T\n0:1,F")

    def test_headerless_sparse_rows_remain_accepted_for_compatibility(self):
        result = self.run_monitor("two_atomic", "0,1\n0\n")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "0:0,T\n0:1,T")


if __name__ == "__main__":
    unittest.main()
