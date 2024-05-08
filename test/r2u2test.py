from __future__ import annotations
from copy import copy
from glob import glob
from pathlib import Path
from typing import Any, Optional

import argparse
import re
import shutil
import sys
import os
import subprocess
import logging
import json


TEST_DIR = Path(__file__).parent
SUITES_DIR = TEST_DIR / "suites"
C2PO_INPUT_DIR = TEST_DIR / "c2po"
TRACE_DIR = TEST_DIR / "trace"
ORACLE_DIR = TEST_DIR / "oracle"
WORK_DIR = TEST_DIR / "__workdir"
DEFAULT_RESULTS_DIR = TEST_DIR / "results"
SPLIT_VERDICTS_SCRIPT = TEST_DIR / "split_verdicts.sh"


class Color:
    HEADER = '\033[95m'
    OKBLUE = '\033[94m'
    OKCYAN = '\033[96m'
    PASS = '\033[92m'
    WARNING = '\033[93m'
    FAIL = '\033[91m'
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'

class Formatter(logging.Formatter):
    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: format_str + ': %(message)s',
        logging.INFO: '%(message)s',
        logging.WARNING: format_str + ': %(message)s',
        logging.ERROR: format_str + ': %(message)s',
        logging.CRITICAL: format_str + ': %(message)s',
    }

    def format(self, record) -> str:
        record.msg = re.sub(r"\033\[\d\d?m", "", record.msg) # removes color from msg
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

class ColorFormatter(logging.Formatter):
    format_str = '%(levelname)s'

    FORMATS = {
        logging.DEBUG: Color.OKBLUE + format_str + Color.ENDC + ': %(message)s',
        logging.INFO: '%(message)s',
        logging.WARNING: Color.WARNING + format_str + Color.ENDC + ': %(message)s',
        logging.ERROR: Color.FAIL + format_str + Color.ENDC + ': %(message)s',
        logging.CRITICAL: Color.UNDERLINE + Color.FAIL + format_str + Color.ENDC + ': %(message)s'
    }

    def format(self, record) -> str:
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

toplevel_logger = logging.getLogger(__name__)
toplevel_logger.setLevel(logging.DEBUG)

stream_handler = logging.StreamHandler(sys.stdout)
stream_handler.setLevel(logging.DEBUG)
stream_handler.setFormatter(ColorFormatter())
toplevel_logger.addHandler(stream_handler)


def cleandir(dir: Path, quiet: bool) -> None:
    """Remove and create fresh dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        os.remove(dir)
    elif dir.is_dir():
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        shutil.rmtree(dir)

    os.mkdir(dir)


def mkdir(dir: Path, quiet: bool) -> None:
    """Remove dir if it is a file then create dir, print a warning if quiet is False"""
    if dir.is_file():
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        os.remove(dir)

    if not dir.is_dir():
        os.mkdir(dir)


def collect_c2po_options(options: dict[str,str|bool]) -> list[str]:
    """Filter all c2po options from suite and return options in a cli-suitable list."""
    c2po_options = []

    if "quiet" in options and options["quiet"]:
        c2po_options.append("--quiet")

    if "impl" in options:
        c2po_options.append("--impl")
        c2po_options.append(options["impl"])

    if "int-width" in options:
        c2po_options.append("--int-width")
        c2po_options.append(options["int-width"])

    if "int-signed" in options and options["int-signed"]:
        c2po_options.append("--int-signed")

    if "float-width" in options:
        c2po_options.append("--float-width")
        c2po_options.append(options["float-width"])

    if "atomic-checkers" in options and options["atomic-checkers"]:
        c2po_options.append("--atomic-checkers")

    if "booleanizer" in options and options["booleanizer"]:
        c2po_options.append("--booleanizer")

    if "disable-cse" in options and options["disable-cse"]:
        c2po_options.append("--disable-cse")

    if "extops" in options and options["extops"]:
        c2po_options.append("--extops")

    if "disable-rewrite" in options and options["disable-rewrite"]:
        c2po_options.append("--disable-rewrite")

    return c2po_options


class TestCase():

    def __init__(
        self, 
        suite_name: str, 
        test_name: Optional[str], 
        mltl_path: Optional[Path], 
        trace_path: Optional[Path], 
        oracle_path: Optional[Path], 
        top_results_dir: Path,
        c2po_options: dict[str,str|bool],
        c2po: Path,
        r2u2bin: Path,
        copyback: bool
    ) -> None:
        self.status = True
        self._copyback = copyback
        self.suite_name: str = suite_name

        if not test_name:
            self.test_fail("No test name given")
            return
        self.test_name: str = test_name

        self.c2po_options: dict[str,str|bool] = c2po_options
        self.top_results_dir: Path = top_results_dir
        self.suite_results_dir: Path = self.top_results_dir / suite_name
        self.test_results_dir: Path = self.suite_results_dir / self.test_name
        self.c2po = c2po
        self.r2u2bin = r2u2bin

        self.clean()
        self.configure_logger()

        if not mltl_path:
            self.test_fail("Invalid MLTL file")
        else:
            self.mltl_path = mltl_path

        if not trace_path:
            self.test_fail("Invalid trace file")
        else:
            self.trace_path = trace_path

        if not oracle_path:
            self.test_fail("Invalid oracle file")
        else:
            self.oracle_path = oracle_path

        self.spec_bin_workdir_path = WORK_DIR / "spec.bin"
        self.spec_bin_path = self.test_results_dir / "spec.bin"

        self.r2u2bin_workdir_log_path = WORK_DIR / "r2u2.log"
        self.r2u2bin_log_path = self.test_results_dir / "r2u2.log"

        self.spec_asm = b""
        self.spec_asm_path = self.test_results_dir / "spec.asm"

        self.c2po_stderr_path = self.test_results_dir / self.c2po.with_suffix(".stderr").name
        self.r2u2bin_stderr_path = self.test_results_dir / self.r2u2bin.with_suffix(".stderr").name

        self.c2po_command_path = self.test_results_dir / self.c2po.with_suffix(".sh").name
        self.r2u2bin_command_path = self.test_results_dir / self.r2u2bin.with_suffix(".sh").name

        self.c2po_cli_options = collect_c2po_options(self.c2po_options)
        self.c2po_command =  ([
            "python3", str(self.c2po)
        ] + collect_c2po_options(self.c2po_options) + 
        [
            "--output", str(self.spec_bin_workdir_path), 
            "--trace", str(self.trace_path),
            str(self.mltl_path)
        ])

        self.r2u2bin_command = [
            str(self.r2u2bin), str(self.spec_bin_workdir_path), str(self.trace_path)
        ]

        if (
            ("booleanizer" not in self.c2po_options or not self.c2po_options["booleanizer"]) and 
            ("atomic-checkers" not in self.c2po_options or not self.c2po_options["atomic-checkers"])  
        ):
            self.r2u2bin_command.append("-a")

    def clean(self) -> None:
        cleandir(self.test_results_dir, False)

    def configure_logger(self) -> None:
        self.logger = logging.getLogger(f"{__name__}_{self.suite_name}_{self.test_name}")
        self.logger.setLevel(logging.DEBUG)

        # note the order matters here -- if we add file_handler first the color
        # gets disabled...unsure why
        stream_handler = logging.StreamHandler(sys.stdout)
        stream_handler.setLevel(logging.DEBUG)
        stream_handler.setFormatter(ColorFormatter())
        self.logger.addHandler(stream_handler)

        file_handler = logging.FileHandler(f"{self.test_results_dir}/test.log")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(Formatter())
        self.logger.addHandler(file_handler)

    def test_fail(self, msg: str) -> None:
        self.logger.info(f"[{Color.FAIL}FAIL{Color.ENDC}] {self.test_name}: {msg}")
        self.status = False
        self.copyback()

    def test_pass(self) -> None:
        self.logger.info(f"[{Color.PASS}PASS{Color.ENDC}] {self.test_name}")
        self.copyback()

    def copyback(self) -> None:
        if not self._copyback:
            return

        shutil.copy(self.mltl_path, self.test_results_dir)
        shutil.copy(self.trace_path, self.test_results_dir)
        shutil.copy(self.oracle_path, self.test_results_dir)

        if self.spec_bin_workdir_path.exists():
            shutil.copy(self.spec_bin_workdir_path, self.test_results_dir)

        with open(self.spec_asm_path, "wb") as f:
            f.write(self.asm)

        c2po_command_new = [
            "python3", str(self.c2po), "--debug"
        ] + collect_c2po_options(self.c2po_options) + \
        [
            "--output", str(self.test_results_dir / self.spec_bin_workdir_path.name), 
            "--trace", str(self.test_results_dir /self.trace_path.name),
            str(self.test_results_dir /self.mltl_path.name)
        ]
        with open(self.c2po_command_path, "w") as f:
            f.write(' '.join(c2po_command_new))

        r2u2bin_command_new = [
            str(self.r2u2bin), 
            str(self.test_results_dir / self.spec_bin_workdir_path.name), 
            str(self.test_results_dir / self.trace_path.name)
        ]

        if (
            ("booleanizer" not in self.c2po_options or not self.c2po_options["booleanizer"]) and 
            ("atomic-checkers" not in self.c2po_options or not self.c2po_options["atomic-checkers"])  
        ):
            r2u2bin_command_new.append("-a")

        with open(self.r2u2bin_command_path, "w") as f:
            f.write(' '.join(r2u2bin_command_new))

    def run(self) -> None:
        if not self.status:
            return

        proc = subprocess.run(self.c2po_command, capture_output=True)

        self.asm = proc.stdout

        if proc.stderr != b"":
            with open(self.c2po_stderr_path, "wb") as f:
                f.write(proc.stderr)

        if proc.returncode != 0:
            self.test_fail(f"c2po.py returned with code {proc.returncode}")
            return

        proc = subprocess.run(self.r2u2bin_command, capture_output=True)

        with open(self.r2u2bin_log_path, "wb") as f:
            f.write(proc.stdout)

        if proc.stderr != b"":
            with open(self.r2u2bin_stderr_path, "wb") as f:
                f.write(proc.stderr)

        if proc.returncode != 0:
            self.test_fail(f"r2u2bin returned with code {proc.returncode}")
            return

        if proc.stdout == b"":
            self.test_fail("No verdicts generated.")
            return

        with open(self.r2u2bin_workdir_log_path, "wb") as f:
            f.write(proc.stdout)

        proc = subprocess.run(["sh", SPLIT_VERDICTS_SCRIPT, self.r2u2bin_workdir_log_path, WORK_DIR])
        proc = subprocess.run(["sh", SPLIT_VERDICTS_SCRIPT, self.oracle_path, WORK_DIR])

        num_formulas = len(glob(f"{self.r2u2bin_workdir_log_path}.*"))
        diffs = []
        for i in range(num_formulas):
            formula_r2u2_log = Path(f"{self.r2u2bin_workdir_log_path}.{i}")
            formula_oracle =  WORK_DIR / f"{self.oracle_path.name}.{i}"

            # if the logs are empty, we treat that the same as it not existing at all
            if not os.path.isfile(formula_r2u2_log):
                formula_r2u2_log.touch()
            if not os.path.isfile(formula_oracle):
                formula_oracle.touch()

            proc = subprocess.run(["diff", formula_r2u2_log, formula_oracle], capture_output=True)

            if proc.returncode != 0:
                diffs.append(i)
                with open(self.test_results_dir / f"{self.test_name}.{i}.diff", "wb") as f:
                    f.write(proc.stdout)

        if len(diffs) > 0:
            self.test_fail(f"Difference with oracle for formulas {diffs}")

        if self.status:
            self.test_pass()

        for f in glob(f"{WORK_DIR}/*"):
            os.remove(f)

        


class TestSuite():

    def __init__(
        self, 
        name: str, 
        top_results_dir: Path,
        c2po: Path,
        r2u2bin: Path,
        copyback: bool
    ) -> None:
        """Initialize TestSuite by cleaning directories and loading JSON data."""
        self.status: bool = True
        self._copyback = copyback
        self.suite_name: str = name
        self.tests: list[TestCase] = []
        self.suites: list[TestSuite] = []
        self.top_results_dir: Path = top_results_dir
        self.suite_results_dir: Path = self.top_results_dir / self.suite_name
        self.c2po = c2po
        self.r2u2bin = r2u2bin

        self.clean()
        self.configure_logger()

        if not c2po.is_file():
            self.suite_fail_msg(f"'c2po' not a file ({c2po}).")

        if not r2u2bin.is_file():
            self.suite_fail_msg(f"'r2u2bin' not a file ({r2u2bin}).")

        self.configure_tests()

    def clean(self) -> None:
        """Clean/create work, results, and suite results directories. 
        Must run this before calling get_suite_logger."""
        cleandir(WORK_DIR, True)
        mkdir(self.top_results_dir, False)
        cleandir(self.suite_results_dir, False)

    def configure_logger(self) -> None:
        self.logger = logging.getLogger(f"{__name__}_{self.suite_name}")
        self.logger.setLevel(logging.DEBUG)

        # note the order matters here -- if we add file_handler first the color
        # gets disabled...unsure why
        stream_handler = logging.StreamHandler(sys.stdout)
        stream_handler.setLevel(logging.DEBUG)
        stream_handler.setFormatter(ColorFormatter())
        self.logger.addHandler(stream_handler)

        file_handler = logging.FileHandler(f"{self.suite_results_dir}/{self.suite_name}.log")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(Formatter())
        self.logger.addHandler(file_handler)

    def suite_fail_msg(self, msg: str) -> None:
        self.logger.error(msg)
        self.logger.info(f"Suite '{self.suite_name}' finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")
        self.status = False

    def suite_fail(self) -> None:
        self.logger.info(f"Suite '{self.suite_name}' finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")
        self.status = False

    def suite_pass(self) -> None:
        self.logger.info(f"Suite '{self.suite_name}' finished with status {Color.BOLD}{Color.PASS}PASS{Color.ENDC}")

    def configure_tests(self) -> None:
        """Configure test suite according to JSON file."""
        config_filename = SUITES_DIR / (self.suite_name + ".json")

        if not config_filename.is_file():
            self.suite_fail_msg(f"Suite configuration file '{config_filename}' does not exist")
            return

        with open(config_filename, "rb") as f:
            config: dict[str, Any] = json.load(f)

        if "tests" not in config and "suites" not in config:
            self.suite_fail_msg(f"No tests specified for suite '{self.suite_name}'")
            return

        if "tests" in config:
            # will be handed off to subprocess.run later
            if "options" not in config:
                self.suite_fail_msg(f"No options specified for suite '{self.suite_name}'")
                return

            self.c2po_options: dict[str,str|bool] = config["options"]

            for testcase in config["tests"]:
                name: Optional[str] = testcase["name"] if "name" in testcase else None
                mltl: Optional[Path] = C2PO_INPUT_DIR / testcase["mltl"] if "mltl" in testcase else None
                trace: Optional[Path] = TRACE_DIR / testcase["trace"] if "trace" in testcase else None
                oracle: Optional[Path] = ORACLE_DIR / testcase["oracle"] if "oracle" in testcase else None

                options = copy(self.c2po_options)
                if "options" in testcase:
                    options.update(testcase["options"])

                self.tests.append(TestCase(self.suite_name, name, mltl, trace, oracle, self.top_results_dir, options, self.c2po, self.r2u2bin, self._copyback))

        if "suites" in config:
            for suite in config["suites"]:
                self.suites.append(TestSuite(suite, self.top_results_dir, self.c2po, self.r2u2bin, self._copyback))

    def run(self) -> int:
        if not self.status:
            return 1
        
        for suite in self.suites:
            suite.run()

        for test in [t for t in self.tests if t.status]:
            test.run()
            self.status = test.status and self.status

        if not self.status:
            self.suite_fail()
            return 1
        else:
            self.suite_pass()
            return 0


def main(c2po: Path, 
         r2u2bin: Path, 
         resultsdir: Path, 
         suite_names: list[str],
         copyback: bool
) -> int:
    suites: list[TestSuite] = []
    for suite_name in suite_names:
        suites.append(TestSuite(suite_name, resultsdir, c2po, r2u2bin, copyback))

    status = 0
    for suite in suites:
        status += suite.run()
    return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--c2po", default=TEST_DIR / "../compiler/c2po.py",
                        help="c2po.py file to use for tests")
    parser.add_argument("--r2u2bin", default=TEST_DIR / "../monitors/static/build/r2u2_debug",
                        help="r2u2 binary to use for tests")
    parser.add_argument("suites", nargs="+",
                        help="names of test suites to run, should be .toml files in suites/")
    parser.add_argument("--resultsdir", default=DEFAULT_RESULTS_DIR,
                        help="directory to output test logs and copyback data")
    parser.add_argument("--copyback", action="store_true",
                        help="copy all source, compiled, and log files from each testcase")
    args = parser.parse_args()

    c2po = Path(args.c2po)
    r2u2bin = Path(args.r2u2bin)
    resultsdir = Path(args.resultsdir)

    retcode = main(c2po, r2u2bin, resultsdir, args.suites, args.copyback)
    sys.exit(retcode)
