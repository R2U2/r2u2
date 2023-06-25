import argparse
import datetime
from glob import glob
from io import TextIOWrapper
import shutil
import tomllib
import os
import subprocess

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

def print_warning(msg: str):
    print(f"{Color.WARNING}WARNING{Color.ENDC}: {msg}")

def print_error(msg: str):
    print(f"{Color.FAIL}ERROR{Color.ENDC}: {msg}")

def print_suite_fail(logfile: TextIOWrapper, suite: str):
    print(f"Suite {suite} finished with status {Color.BOLD}{Color.FAIL}FAIL{Color.ENDC}")
    logfile.write(f"Suite {suite} finished with status FAIL\n")

def print_suite_pass(logfile: TextIOWrapper, suite: str):
    print(f"Suite {suite} finished with status {Color.BOLD}{Color.PASS}PASS{Color.ENDC}")
    logfile.write(f"Suite {suite} finished with status PASS\n")

def print_test_fail(logfile: TextIOWrapper, testname: str, msg: str):
    print(f"{testname} [{Color.FAIL}FAIL{Color.ENDC}] {msg}") 
    logfile.write(f"{testname} [FAIL] {msg}\n") 

def print_test_pass(logfile: TextIOWrapper, testname: str, msg: str):
    print(f"{testname} [{Color.PASS}PASS{Color.ENDC}] {msg}") 
    logfile.write(f"{testname} [PASS] {msg}\n") 

def cleandir(dir: str, quiet: bool):
    """Remove and create fresh dir, print a warning if quiet is False"""
    if os.path.isfile(dir):
        if not quiet:
            print_warning(f"Overwriting '{dir}'")
        os.remove(dir)
    elif os.path.isdir(dir):
        if not quiet:
            print_warning(f"Overwriting '{dir}'")
        shutil.rmtree(dir)

    os.mkdir(dir)

def mkdir(dir: str, quiet: bool):
    """Remove dir if it is a file then create dir, print a warning if quiet is False"""
    if os.path.isfile(dir):
        if not quiet:
            print_warning(f"Overwriting '{dir}'")
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

def run_suite(r2u2prep: str, 
         r2u2bin: str, 
         resultsdir: str, 
         suite: str,
         copyback: bool
) -> None:
    suite_status = True

    # clean up directory structure
    cleandir(WORK_DIR, True)
    mkdir(resultsdir, False)
    cleandir(f"{resultsdir}/{suite}", False)

    logfile = open(f"{resultsdir}/{suite}/{suite}.log", "w")
    logfile.write(f"Executing suite {suite} at {datetime.datetime.now()}\n")

    # validate suite config file
    suite_config_filename = SUITES_DIR + suite + ".toml"
    if not os.path.isfile(suite_config_filename):
        print_error( f"Suite configuration file '{suite_config_filename}' does not exist")
        print_suite_fail(logfile, suite)
        return
    
    with open(suite_config_filename, "rb") as f:
        config = tomllib.load(f)

        spec_bin = WORK_DIR + "r2u2_spec.bin"
        r2u2_log = WORK_DIR + "__r2u2.log"

        # will be handed off to subprocess.run later
        r2u2prep_options = collect_r2u2prep_options(config["options"]) 

        if not config["tests"]:
            print_error(f"No 'tests' specified for suite '{suite}'")
            print_suite_fail(logfile, suite)
            return

        for testname,testcase in config["tests"].items():
            test_status = True

            testresultsdir = f"{resultsdir}/{suite}/{testname}"
            cleandir(testresultsdir, False)

            if "mltl" not in testcase:
                print_test_fail(logfile, testname, f"No mltl file specified in '{suite_config_filename}'")
                suite_status = False
                continue
            mltl = MLTL_DIR + testcase["mltl"]

            if "trace" not in testcase:
                print_test_fail(logfile, testname, f"No trace file specified in '{suite_config_filename}'")
                suite_status = False
                continue
            trace = TRACE_DIR + testcase["trace"]

            if "oracle" not in testcase:
                print_test_fail(logfile, testname, f"No oracle file specified in '{suite_config_filename}'")
                suite_status = False
                continue
            oracle = ORACLE_DIR + testcase["oracle"]

            proc = subprocess.run(["python3", r2u2prep] + r2u2prep_options + 
                ["--output-file", spec_bin, mltl, trace], capture_output=True)

            with open(f"{testresultsdir}/r2u2_spec.asm", "wb") as f:
                f.write(proc.stdout)

            if proc.stderr != b"":
                with open(f"{testresultsdir}/r2u2prep.py.stderr", "wb") as f:
                    f.write(proc.stderr)

            if proc.returncode != 0:
                print_test_fail(logfile, testname, f"r2u2prep.py returned with code {proc.returncode}")
                suite_status = False
                continue

            proc = subprocess.run([r2u2bin, spec_bin, trace], capture_output=True)

            with open(f"{testresultsdir}/r2u2.log", "wb") as f:
                f.write(proc.stdout)

            if proc.stderr != b"":
                with open(f"{testresultsdir}/r2u2.stderr", "wb") as f:
                    f.write(proc.stderr)

            if proc.returncode != 0:
                print_test_fail(logfile, testname, f"r2u2bin returned with code {proc.returncode}")
                suite_status = False
                continue

            with open(r2u2_log, "wb") as f:
                f.write(proc.stdout)

            proc = subprocess.run([SPLIT_VERDICTS_SCRIPT, r2u2_log, WORK_DIR])
            proc = subprocess.run([SPLIT_VERDICTS_SCRIPT, oracle, WORK_DIR])

            for i in range(len(glob(r2u2_log+".[0-9]*"))):
                formula_r2u2_log = r2u2_log + f".{i}"
                formula_oracle = WORK_DIR + testcase["oracle"] + f".{i}"

                # note that we are walking thru each generated .log files,
                # NOT the oracle files, so if we have extra oracles we do nothing
                if not os.path.isfile(formula_oracle):
                    with open(formula_oracle, "w") as f: pass

                proc = subprocess.run(["diff", formula_r2u2_log, formula_oracle], capture_output=True)

                if proc.returncode != 0:
                    print_test_fail(logfile, testname, f"Difference with oracle for formula {i}")
                    test_status = False
                    with open(f"{testresultsdir}/{testcase['oracle']}.{i}.diff", "wb") as f:
                        f.write(proc.stdout)

            if test_status:
                print_test_pass(logfile, testname, "")
            else:
                suite_status = False

            if copyback:
                shutil.copy(mltl, testresultsdir)
                shutil.copy(trace, testresultsdir)
                shutil.copy(oracle, testresultsdir)
                shutil.copy(spec_bin, testresultsdir)

            for f in glob(f"{WORK_DIR}/*"):
                os.remove(f)
    
    if suite_status:
        print_suite_pass(logfile, suite)
    else:
        print_suite_fail(logfile, suite)

    logfile.close()


def main(r2u2prep: str, 
         r2u2bin: str, 
         resultsdir: str, 
         suites: list[str],
         copyback: bool
) -> None:
    for suite in suites:
        run_suite(r2u2prep, r2u2bin, resultsdir, suite, copyback)


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
