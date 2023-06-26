from __future__ import annotations
from glob import glob
from io import TextIOWrapper
from pathlib import Path
from typing import Any

import argparse
import datetime
import re
import shutil
import sys
import tomllib
import os
import subprocess
import logging
from typing_extensions import Self
from xml.dom.pulldom import parseString
from xmlrpc.client import FastParser

CWD = os.getcwd()
SUITES_DIR = CWD+"/suites/"
MLTL_DIR = CWD+"/mltl/"
TRACE_DIR = CWD+"/input/"
ORACLE_DIR = CWD+"/oracle/"
WORK_DIR = CWD+"/__workdir/"
SPLIT_VERDICTS_SCRIPT = CWD+"/split_verdicts.sh"

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

    def format(self, record):
        log_fmt = self.FORMATS.get(record.levelno)
        formatter = logging.Formatter(log_fmt)
        return formatter.format(record)

toplevel_logger = logging.getLogger(__name__)
toplevel_logger.setLevel(logging.DEBUG)

stream_handler = logging.StreamHandler(sys.stdout)
stream_handler.setLevel(logging.DEBUG)
stream_handler.setFormatter(ColorFormatter())
toplevel_logger.addHandler(stream_handler)

def cleandir(dir: str, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if os.path.isfile(dir):
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        os.remove(dir)
    elif os.path.isdir(dir):
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        shutil.rmtree(dir)

    os.mkdir(dir)


def mkdir(dir: str, quiet: bool):
    """Remove dir if it is a file then create dir, print a warning if quiet is False"""
    if os.path.isfile(dir):
        if not quiet:
            toplevel_logger.warning(f"Overwriting '{dir}'")
        os.remove(dir)

    if not os.path.isdir(dir):
        os.mkdir(dir)


def collect_r2u2prep_options(options: dict[str,str|bool]) -> list[str]:
    """Filter all r2u2prep options from suite and return options in a cli-suitable list."""
    r2u2prep_options = []

    if "quiet" in options and options["quiet"]:
        r2u2prep_options.append("--quiet")

    if "implementation" in options:
        r2u2prep_options.append("--implementation")
        r2u2prep_options.append(options["implementation"])

    if "int-width" in options:
        r2u2prep_options.append("--int-width")
        r2u2prep_options.append(options["int-width"])

    if "int-signed" in options and options["int-signed"]:
        r2u2prep_options.append("--int-signed")

    if "float-width" in options:
        r2u2prep_options.append("--float-width")
        r2u2prep_options.append(options["float-width"])

    if "atomic-checker" in options and options["atomic-checker"]:
        r2u2prep_options.append("--atomic-checker")

    if "booleanizer" in options and options["booleanizer"]:
        r2u2prep_options.append("--booleanizer")

    if "disable-cse" in options and options["disable-cse"]:
        r2u2prep_options.append("--disable-cse")

    if "extops" in options and options["extops"]:
        r2u2prep_options.append("--extops")

    if "disable-rewrite" in options and options["disable-rewrite"]:
        r2u2prep_options.append("--disable-rewrite")

    return r2u2prep_options


class TestCase():

    def __init__(self, 
                 suite_name: str, 
                 test_name: str, 
                 mltl_filename: str, 
                 trace_filename: str, 
                 oracle_filename: str, 
                 r2u2prep_options: list[str],
                 top_results_dir: str):
        self.status = True
        self.suite_name: str = suite_name
        self.test_name: str = test_name
        self.r2u2prep_options: list[str] = r2u2prep_options
        self.top_results_dir: str = top_results_dir
        self.suite_results_dir: str = f"{top_results_dir}/{suite_name}"
        self.test_results_dir: str = f"{self.suite_results_dir}/{test_name}"

        self.clean()
        self.configure_logger()

        if mltl_filename == "":
            self.test_fail(f"Invalid MLTL file")
        if trace_filename == "":
            self.test_fail(f"Invalid trace file")
        if oracle_filename == "":
            self.test_fail(f"Invalid oracle file")

        self.mltl_path = Path(f"{MLTL_DIR}/{mltl_filename}")
        self.trace_path = Path(f"{TRACE_DIR}/{trace_filename}")
        self.oracle_path = Path(f"{ORACLE_DIR}/{oracle_filename}")
        self.spec_bin = Path(f"{WORK_DIR}/r2u2_spec.bin")
        self.r2u2_log = Path(f"{WORK_DIR}/r2u2.log")


    def clean(self):
        cleandir(self.test_results_dir, False)


    def configure_logger(self):
        self.logger = logging.getLogger(f"{__name__}_{self.suite_name}_{self.test_name}")
        self.logger.setLevel(logging.DEBUG)

        # note the order matters here -- if we add file_handler first the color
        # gets disabled...unsure why
        stream_handler = logging.StreamHandler(sys.stdout)
        stream_handler.setLevel(logging.DEBUG)
        stream_handler.setFormatter(ColorFormatter())
        self.logger.addHandler(stream_handler)

        file_handler = logging.FileHandler(f"{self.test_results_dir}/{self.test_name}.log")
        file_handler.setLevel(logging.DEBUG)
        file_handler.setFormatter(Formatter())
        self.logger.addHandler(file_handler)


    def test_fail(self, msg: str):
        self.logger.info(f"{self.test_name} [{Color.FAIL}FAIL{Color.ENDC}] {msg}")
        self.status = False


    def test_pass(self, msg: str):
        self.logger.info(f"{self.test_name} [{Color.PASS}PASS{Color.ENDC}] {msg}")


    def run(self, r2u2prep: str, r2u2bin: str, copyback: bool):
        proc = subprocess.run(["python3", r2u2prep] + self.r2u2prep_options + 
                ["--output-file", self.spec_bin, self.mltl_path, self.trace_path], capture_output=True)

        with open(f"{self.test_results_dir}/r2u2_spec.asm", "wb") as f:
            f.write(proc.stdout)

        if proc.stderr != b"":
            with open(f"{self.test_results_dir}/r2u2prep.py.stderr", "wb") as f:
                f.write(proc.stderr)

        if proc.returncode != 0:
            self.test_fail(f"r2u2prep.py returned with code {proc.returncode}")
            return

        proc = subprocess.run([r2u2bin, self.spec_bin, self.trace_path], capture_output=True)

        with open(f"{self.test_results_dir}/r2u2.log", "wb") as f:
            f.write(proc.stdout)

        if proc.stderr != b"":
            with open(f"{self.test_results_dir}/r2u2.stderr", "wb") as f:
                f.write(proc.stderr)

        if proc.returncode != 0:
            self.test_fail(f"r2u2bin returned with code {proc.returncode}")
            return

        with open(self.r2u2_log, "wb") as f:
            f.write(proc.stdout)

        proc = subprocess.run([SPLIT_VERDICTS_SCRIPT, self.r2u2_log, WORK_DIR])
        proc = subprocess.run([SPLIT_VERDICTS_SCRIPT, self.oracle_path, WORK_DIR])

        for i in range(len(glob(f"{self.r2u2_log}.[0-9]*"))):
            formula_r2u2_log = f"{self.r2u2_log}.{i}"
            formula_oracle =  f"{WORK_DIR}/{self.oracle_path.name}.{i}"

            # note that we are walking thru each generated .log files,
            # NOT the oracle files, so if we have extra oracles we do nothing
            if not os.path.isfile(formula_oracle):
                with open(formula_oracle, "w") as f: pass

            proc = subprocess.run(["diff", formula_r2u2_log, formula_oracle], capture_output=True)

            if proc.returncode != 0:
                self.test_fail(f"Difference with oracle for formula {i}")
                with open(f"{self.test_results_dir}/{self.test_name}.{i}.diff", "wb") as f:
                    f.write(proc.stdout)

        if self.status:
            self.test_pass("")

        if copyback:
            shutil.copy(self.mltl_path, self.test_results_dir)
            shutil.copy(self.trace_path, self.test_results_dir)
            shutil.copy(self.oracle_path, self.test_results_dir)
            shutil.copy(self.spec_bin, self.test_results_dir)

        for f in glob(f"{WORK_DIR}/*"):
            os.remove(f)


class TestSuite():

    def __init__(self, name: str, top_results_dir: str) -> None:
        """Initialize TestSuite by cleaning directories and loading TOML data."""
        self.status: bool = True
        self.suite_name: str = name
        self.tests: list[TestCase] = []
        self.top_results_dir: str = top_results_dir
        self.suite_results_dir: str = f"{top_results_dir}/{self.suite_name}"
        
        self.clean()
        self.configure_logger()
        self.configure_tests()

    def clean(self):
        """Clean/create work, results, and suite results directories. 
        Must run this before calling get_suite_logger."""
        cleandir(WORK_DIR, True)
        mkdir(self.top_results_dir, False)
        cleandir(self.suite_results_dir, False)

    def configure_logger(self):
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

    def suite_fail_msg(self, msg: str):
        self.logger.error(msg)
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")

    def suite_fail(self):
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")

    def suite_pass(self):
        self.logger.info(f"Suite {self.suite_name} finished with status {Color.BOLD}{Color.PASS}PASS{Color.ENDC}")

    def configure_tests(self):
        """Configure test suite according to TOML file."""
        config_filename = SUITES_DIR + self.suite_name + ".toml"

        if not os.path.isfile(config_filename):
            self.suite_fail_msg(f"Suite configuration file '{config_filename}' does not exist")
            return

        with open(config_filename, "rb") as f:
            config: dict[str, Any] = tomllib.load(f)

        # will be handed off to subprocess.run later
        if "options" not in config:
            self.suite_fail_msg(f"No options specified for suite '{self.suite_name}'")
            return

        self.r2u2prep_options: list[str] = collect_r2u2prep_options(config["options"]) 

        if "tests" not in config:
            self.suite_fail_msg(f"No tests specified for suite '{self.suite_name}'")
            return

        for test_name,testcase in config["tests"].items():
            mltl: str = "" if "mltl" not in testcase else testcase["mltl"]
            trace: str = "" if "trace" not in testcase else testcase["trace"]
            oracle: str = "" if "oracle" not in testcase else testcase["oracle"]

            self.tests.append(TestCase(self.suite_name, test_name, mltl, trace, oracle, self.r2u2prep_options, self.top_results_dir))

    def run(self, r2u2prep: str, r2u2bin: str, copyback: bool):
        if not self.status:
            return

        for test in self.tests:
            test.run(r2u2prep, r2u2bin, copyback)
            self.status = test.status and self.status

        if not self.status:
            self.suite_fail()
        else:
            self.suite_pass()


def main(r2u2prep: str, 
         r2u2bin: str, 
         results_dir: str, 
         suite_names: list[str],
         copyback: bool):
    suites: list[TestSuite] = []
    for suite_name in suite_names:
        suites.append(TestSuite(suite_name, results_dir))

    for suite in suites:
        suite.run(r2u2prep, r2u2bin, copyback)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("r2u2prep",
                        help="r2u2_prep.py file to use for tests")
    parser.add_argument("r2u2bin",
                        help="r2u2 binary to use for tests")
    parser.add_argument("resultsdir",
                        help="directory to output test logs and copyback data")
    parser.add_argument("suites", nargs="+",
                        help="names of test suites to run, should be .toml files in suites/")
    parser.add_argument("--copyback", action="store_true",
                        help="copy all source, compiled, and log files from each testcase")
    args = parser.parse_args()

    main(args.r2u2prep, args.r2u2bin, args.resultsdir, args.suites, args.copyback)
