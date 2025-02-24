import matplotlib.pyplot as plt
import csv
import itertools
import argparse

plt.rcParams.update({"font.family": "serif", "font.size": 12})

parser = argparse.ArgumentParser(description="Plot results from a set of benchmarks")
parser.add_argument("benchmarks", type=str, help="File containing list of benchmarks")
parser.add_argument("output", type=str, help="File to save the plot")
parser.add_argument("-vb", action="store_true", help="Include virtual best")
parser.add_argument("-log", action="store_true", help="Use logarithmic scale")
parser.add_argument("-mark", action="store_true", help="Use markers")
args = parser.parse_args()

with open(args.benchmarks, "r") as f:
    benchmarks = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["benchmarkname"]["testname"] = ("result", "time")
results: dict[str, dict[str, float]] = {}

if args.vb:
    results["virtual_best"] = {}

# CSV files are of the form:
# "filename", "status", "encoding-time", "sat-result", "sat-time", "calls"
for benchmark in benchmarks:
    results[benchmark] = {}
    with open(benchmark, newline="") as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            testname = row[0]
            if row[3] == "sat" or row[3] == "unsat":
                results[benchmark][testname] = float(row[4])
                if args.vb:
                    if testname in results["virtual_best"]:
                        results["virtual_best"][testname] = min(
                            results["virtual_best"][testname], float(row[4])
                        )
                    else:
                        results["virtual_best"][testname] = float(row[4])

sorted: dict[str, list[float]] = {b: sorted(r.values()) for b, r in results.items()}

fig, ax = plt.subplots(figsize=(12, 6))

for benchmark in results.keys():
    sorted[benchmark] = list(itertools.accumulate(sorted[benchmark]))
    sorted[benchmark] = [x / 60 for x in sorted[benchmark]]
    # sorted[benchmark] = sorted[benchmark][0::10]

    fmt = ""
    if ".uflia" in benchmark:
        fmt += "*-" if args.mark else "-"
    elif ".auflia" in benchmark:
        fmt += "o-" if args.mark else "-"
    elif ".qf_auflia" in benchmark:
        fmt += "v-" if args.mark else "-"
    elif ".aufbv" in benchmark:
        fmt += "s-" if args.mark else "-"
    elif ".qf_aufbv" in benchmark:
        fmt += "x-" if args.mark else "-"
    elif ".qf_bv_incr" in benchmark:
        fmt += "P-" if args.mark else "-"
    elif ".qf_bv" in benchmark: 
        fmt += "D-" if args.mark else "-"     

    if "z3" in benchmark:
        fmt += "b"
    elif "cvc5" in benchmark:
        fmt += "g"
    elif "yices" in benchmark:
        fmt += "r"
    elif "bitwuzla" in benchmark:
        fmt += "c"

    if "virtual_best" in benchmark:
        fmt += "h-k" if args.mark else "-k"

    ax.plot(
        sorted[benchmark], range(len(sorted[benchmark])), fmt, linewidth=(1 if args.mark else 3), markersize=5
    )

# ax.set_xticks(range(0, len(sorted[benchmarks[0]]), 5))
# ax.set_xticklabels([str(x * 300) for x in range(0, len(sorted[benchmarks[0]]), 5)])

box = ax.get_position()
ax.set_position((box.x0, box.y0, box.width * 0.7, box.height))

if args.log:
    ax.set_yscale("log")

plt.legend(
    [
        b.removeprefix("results/").removesuffix(".csv").replace("yices-smt2", "yices2")
        for b in results.keys()
    ],
    loc="center left",
    bbox_to_anchor=(1, 0.5),
)
plt.xlabel("Time (min)")
plt.ylabel("Number solved")
plt.savefig(args.output)
