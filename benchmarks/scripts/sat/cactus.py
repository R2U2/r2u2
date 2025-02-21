import matplotlib.pyplot as plt
import csv
import itertools
import argparse

plt.rcParams.update({'font.family': 'serif', 'font.size': 12})

parser = argparse.ArgumentParser(description="Plot results from a set of benchmarks")
parser.add_argument("benchmarks", type=str, help="File containing list of benchmarks")
parser.add_argument("output", type=str, help="File to save the plot")
parser.add_argument("-vb", action="store_true", help="Include virtual best")
parser.add_argument("-log", action="store_true", help="Use logarithmic scale")
args = parser.parse_args()

with open(args.benchmarks, "r") as f:
    benchmarks = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["benchmarkname"]["testname"] = ("result", "time")
results: dict[str, dict[str, float]] = {}

if args.vb:
    results["virtual_best"] = {}

# CSV files are of the form:
# "filename", "status", "result", "time", "calls"
for benchmark in benchmarks:
    results[benchmark] = {}
    with open(benchmark, newline="") as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            testname = row[0]
            if row[3] == "sat" or row[3] == "unsat":
                results[benchmark][testname] = (float(row[4]))
                if args.vb:
                    if testname in results["virtual_best"]:
                        results["virtual_best"][testname] = min(results["virtual_best"][testname], float(row[4]))
                    else:
                        results["virtual_best"][testname] = float(row[4])

sorted: dict[str, list[float]] = { b:sorted(r.values()) for b,r in results.items() }

fig, ax = plt.subplots(figsize=(12, 6))

for benchmark in results.keys():
    sorted[benchmark] = list(itertools.accumulate(sorted[benchmark]))
    sorted[benchmark] = sorted[benchmark][0::300]

    fmt = ""
    if ".uflia" in benchmark:
        fmt += "*-"
    elif ".auflia" in benchmark:
        fmt += "o-"
    elif ".qf_auflia" in benchmark:
        fmt += "v-"
    elif ".aufbv" in benchmark:
        fmt += "s-"
    elif ".qf_aufbv" in benchmark:
        fmt += "x-"
    elif ".qf_bv" in benchmark:
        fmt += "D-"

    if "z3" in benchmark:
        fmt += "b"
    elif "cvc5" in benchmark:
        fmt += "g"
    elif "yices" in benchmark:
        fmt += "r"
    elif "bitwuzla" in benchmark:
        fmt += "c"

    if "virtual_best" in benchmark:
        fmt += "h-k"

    ax.plot(range(len(sorted[benchmark])), sorted[benchmark], fmt, linewidth=1, markersize=5)

ax.set_xticks(range(0, len(sorted[benchmarks[0]]), 5))
ax.set_xticklabels([str(x * 300) for x in range(0, len(sorted[benchmarks[0]]), 5)])

box = ax.get_position()
ax.set_position((box.x0, box.y0, box.width * 0.7, box.height))

if args.log:
    ax.set_yscale('log')

plt.legend([b.removeprefix("results/").removesuffix(".csv").replace("yices-smt2", "yices2") for b in results.keys()], loc="center left", bbox_to_anchor=(1, 0.5))
plt.xlabel("Number solved")
plt.ylabel("Time (min)")
plt.savefig(args.output)
