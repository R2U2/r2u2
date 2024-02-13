"""
Reads cleaned HTML source from here: https://temporallogic.org/research/DETECT2020/results.html

Outputs MLTL files based on specs listed.
"""
import re

from pathlib import Path

CURDIR = Path(__file__).parent
MLTL_DIR = CURDIR / "mltl"
CSV_DIR = CURDIR / "trace"


with open("results.html", "r") as f:
    s = f.read()

# labels = [l for l in s.split("<td>") if "href" in l]
# labels = [re.search("(?<=html[>] )\w+", l).group() for l in labels]

for row in s.split("<tr>"):
    props = set()

    cells = row.split("<td>")
    if len(cells) < 3:
        continue

    m = re.search(r"(?<=html[>] )\w+", cells[1])
    if m:
        label = m.group()
    else:
        label = ""
        
    m = re.search(".*(?=[<][/]td[>])", cells[3])
    if m:
        formula = m.group()
        formula = formula.strip()
        formula = formula.replace("&not;", "!")
        formula = formula.replace("&and;", "&&")
        formula = formula.replace("&or;", "||")
        formula = formula.replace("&rarr;", "->")
        formula = formula.replace("&#9744;", "G")
        formula = formula.replace("&#9826;", "F")
        formula = formula.replace(".", "_")

        formula.replace("G ", "")
    else:
        formula = ""

    for m in re.finditer(r"\w+", formula):
        p = m.group()
        if p == "G" or p == "F" or p == "M" or p.isdigit():
            continue
        props.add(p)

    with open(MLTL_DIR / f"{label}.mltl", "w") as f:
        f.write("INPUT\n\t")
        f.write(",".join(props))
        f.write(": bool;\n\n")

        f.write(f"FTSPEC\n\t{formula};")
        
    with open(CSV_DIR / f"{label}.csv", "w") as f:
        f.write("# ")
        f.write(",".join(props))
        f.write("\n")
        # for i in range(0,100):
        #     row = ",".join([str(random.randint(0,1)) for r in props])
        #     f.write(row + "\n")
