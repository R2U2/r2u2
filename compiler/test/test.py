import pathlib
import json
import difflib
import subprocess

TEST_DIR = pathlib.Path(__file__).parent

C2PO_PATH = TEST_DIR / ".." / "c2po.py"
MAP_PATH = TEST_DIR / "default.map"
CONFIG_PATH = TEST_DIR / "config.json"


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
    print(f"[{Color.FAIL}PASS{Color.ENDC}] {msg}")


def run_test(test: dict) -> None:
    """Runs and prints status of `test` where `test` looks like:

    `{
        "input": "file.c2po",
        "expected_output": "file.c2po.expect",
        "options": ["opt", ...]
    }`

    See `config.json`.
    """
    command = ["python3", str(C2PO_PATH.absolute())] + test["options"] + [test["input"]]
    proc = subprocess.run(command, capture_output=True)
    test_output = proc.stdout.decode().splitlines(keepends=True)

    with open(test["expected_output"], "r") as f:
        expected_output = f.read().splitlines(keepends=True)

    result = difflib.unified_diff(
        expected_output,
        test_output,
        fromfile=test["input"],
        tofile=test["expected_output"],
    )

    diff = ""
    status = True
    for line in result:
        if line[0] in {"-", "+", "?"}:
            status = False
        diff += line

    if status:
        print_pass(f"{test['input']}")
    else:
        print_fail(f"{test['input']}\n{diff}")

    return


if __name__ == "__main__":
    # tests is an array of JSON objects
    with open(str(CONFIG_PATH), "r") as f:
        tests = json.load(f)

    [run_test(test) for test in tests]
