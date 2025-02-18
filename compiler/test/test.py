import pathlib
import json
import difflib
import subprocess
import sys
import argparse

TEST_DIR = pathlib.Path(__file__).parent

C2PO_PATH = TEST_DIR / ".." / "c2po.py"
MAP_PATH = TEST_DIR / "default.map"
CONFIG_PATH = TEST_DIR / "config.json"
OUTPUT_PATH = TEST_DIR / "output" # assume that all serialized output is written to a file named 'output'


class Color:
    HEADER = "\033[95m"
    OKBLUE = "\033[94m"
    OKCYAN = "\033[96m"
    PASS = "\033[92m"
    WARNING = "\033[93m"
    FAIL = "\033[91m"
    ENDC = "\033[0m"
    BOLD = "\033[1m"
    UNDERLINE = "\033[4m"


def print_pass(msg: str):
    print(f"[{Color.PASS}PASS{Color.ENDC}] {msg}")


def print_fail(msg: str):
    print(f"[{Color.FAIL}FAIL{Color.ENDC}] {msg}")


def run_diff(
    expected_output: "list[str]", test_output: "list[str]", fromfile: str, tofile: str
) -> "tuple[bool, str]":
    """Returns a pair whose first element is True if the `expected_output` and `test_output` are the same and False otherwise, and whose second element is the diff between `expected_output` and `test_output`."""
    result = difflib.unified_diff(
        expected_output,
        test_output,
        fromfile=fromfile,
        tofile=tofile,
    )

    status = True
    diff = ""
    for line in result:
        if line[0] in {"-", "+", "?"}:
            status = False
        diff += line

    return (status, diff)


def run_test(test: dict) -> bool:
    """Runs and prints status of `test` where `test` looks like:

    `{
        "input": "file.c2po",
        "expected_output": "file.c2po.expect",
        "options": ["opt", ...]
    }`

    See `config.json`.
    """
    status, bad_file, diff = True, False, ""

    command = ["python3", str(C2PO_PATH.absolute())] + test["options"] + [test["input"]]

    proc = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    try:
        if "expected_output" in test:
            # Both stdout and stderr are captured in proc.stdout
            test_output = proc.stdout.decode().splitlines(keepends=True)

            with open(test["expected_output"], "r") as f:
                expected_output = f.read().splitlines(keepends=True)

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_output"]
            )
        elif "expected_c2po" in test:
            with open(str(OUTPUT_PATH), "r") as f:
                test_output = f.read().splitlines(keepends=True)

            with open(test["expected_c2po"], "r") as f:
                expected_output = f.read().splitlines(keepends=True)

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_c2po"]
            )

            OUTPUT_PATH.unlink()
        elif "expected_mltl" in test:
            with open(str(OUTPUT_PATH), "r") as f:
                test_output = f.read().splitlines(keepends=True)

            with open(test["expected_mltl"], "r") as f:
                expected_output = f.read().splitlines(keepends=True)

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_mltl"]
            )

            OUTPUT_PATH.unlink()
        elif "expected_prefix" in test:
            with open(str(OUTPUT_PATH), "r") as f:
                test_output = f.read().splitlines(keepends=True)

            with open(test["expected_prefix"], "r") as f:
                expected_output = f.read().splitlines(keepends=True)

            status, diff = run_diff(
                expected_output, test_output, test["input"], test["expected_prefix"]
            )

            OUTPUT_PATH.unlink()
    except FileNotFoundError:
        status = False
        bad_file = True

    if status:
        print_pass(f"{test['input']}")
    elif diff == "":
        print_fail(f"{test['input']}\nCommand: {' '.join(command)}")
    else:
        print_fail(f"{test['input']}\nCommand: {' '.join(command)}\n{diff}")

    if bad_file:
        print("Expected output or actual output file does not exist.")

    return status


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("subset", nargs="?", default="",
                        help="name of subset to run")
    args = parser.parse_args()

    # tests is an array of JSON objects
    with open(str(CONFIG_PATH), "r") as f:
        config = json.load(f)

    if args.subset == "":
        # no subset given, so concatenate all the tests together
        # tests = {name:s for name,arr in config.items() for s in arr}
        tests = config
    elif args.subset in config:
        tests = {args.subset: config[args.subset]}
    else:
        print_fail(f"Subset '{args.subset}' not in {CONFIG_PATH}")
        sys.exit(1)

    num_failed = 0
    for subset_name,tests in tests.items():
        print('{:*^80}'.format(f" Subset '{subset_name}' "))
        num_failed += sum([not run_test(test) for test in tests])

    sys.exit(num_failed)
