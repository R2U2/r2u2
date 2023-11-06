import argparse
import re

from typing import Set
from pathlib import Path

def main(input_path: Path, output_path: Path):
    with open(input_path, "r") as f:
        content = f.read()

    props: Set[str] = Set()
    mltl = content

    mltl = mltl.replace("&", "&&")
    mltl = mltl.replace("|", "||")

    for m in re.finditer(r"\w+", mltl):
        p = m.group()
        if p == "G" or p == "F" or p.isdigit() or p == "false" or p == "true":
            continue
        props.add(p)

    with open(output_path, "w") as f:
        f.write("INPUT\n\t")
        f.write(",".join(props))
        f.write(": bool;\n\n")

        f.write("FTSPEC\n\t")
        f.write(mltl + ";")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("input", help="input mltl file")
    parser.add_argument("--output", help="output c2po file")

    args = parser.parse_args()

    input_path = Path(args.input)
    output_path = Path(args.output) if args.output else input_path.with_suffix(".c2po")

    main(input_path, output_path)