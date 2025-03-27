import matplotlib.pyplot as plt
import csv
import itertools
import argparse

plt.rcParams.update({"font.family": "serif", "font.size": 10})

parser = argparse.ArgumentParser(description="plot results from a set of benchmarks")
parser.add_argument("benchmarks", type=str, help="file containing list of benchmarks")
parser.add_argument("output", type=str, help="file to save the plot")
parser.add_argument("-vb", action="store_true", help="include virtual best")
parser.add_argument("-log", action="store_true", help="use logarithmic scale")
parser.add_argument("-mark", action="store_true", help="use markers")
parser.add_argument("-linestyle", action="store_true", help="use linestyles to differentiate benchmark sizes")
args = parser.parse_args()

with open(args.benchmarks, "r") as f:
    benchmarks = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["benchmarkname"]["testname"] = ("result", "time")
results: dict[str, dict[str, float]] = {}

if args.vb:
    results["__virtual_best__"] = {}

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
                    if testname in results["__virtual_best__"]:
                        results["__virtual_best__"][testname] = min(
                            results["__virtual_best__"][testname], float(row[4])
                        )
                    else:
                        results["__virtual_best__"][testname] = float(row[4])

sorted_data: dict[str, list[float]] = {b: sorted(r.values()) for b,r in results.items()}

fig, ax = plt.subplots(layout="tight", figsize=(6,3))

for benchmark in results.keys():
    sorted_data[benchmark] = list(itertools.accumulate(sorted_data[benchmark]))
    sorted_data[benchmark] = [x / 60 for x in sorted_data[benchmark]]

    color = ""
    linestyle = ""
    marker = ""
    linewidth = 2
    if ".uflia" in benchmark:
        color = "darkgoldenrod" 
        linestyle = "solid"
    elif ".qf_uflia" in benchmark:
        color = "darkorchid" 
        linestyle = "solid"
    elif ".qf_bv_incr" in benchmark:
        color = "blue" 
        linestyle = "solid"
    elif ".qf_bv" in benchmark: 
        color = "red"    
        linestyle = "solid"
    elif "__virtual_best__" in benchmark:
        color = "black"
        linestyle = "solid"

    if args.linestyle:
        if "10000" in benchmark:
            linestyle = "solid"
        elif "1000" in benchmark:
            linestyle = "dashdot"
        elif "100" in benchmark:
            linestyle = "dashed"
        elif "10" in benchmark:
            linestyle = "dotted"

    ax.plot(
        sorted_data[benchmark], range(len(sorted_data[benchmark])), color=color, linewidth=linewidth, linestyle=linestyle,
        marker=marker if args.mark else None,
        markevery=500 if args.mark else None,
    )

if args.log:
    ax.set_yscale("log")

plt.legend(
    [
        b.removeprefix("results/")
        .removesuffix(".csv")
        .replace("yices-smt2", "yices2")
        .replace("vb.", "")
        .replace("qf_bv_incr.", "QF_BV_incr-")
        .replace("qf_bv.", "QF_BV-")
        .replace("qf_uflia.", "QF_UFLIA-")
        .replace("uflia.", "UFLIA-")
        .replace("random-10", "10")
        .replace("random-100", "100")
        .replace("random-1000", "1000")
        .replace("random-10000", "10000")
        .replace("__virtual_best__", "Virtual best")
        for b in results.keys()
    ],
    loc="lower right",
)
plt.xlabel("Cumulative Time (min)")
plt.ylabel("Number solved")
plt.savefig(args.output, dpi=300)
