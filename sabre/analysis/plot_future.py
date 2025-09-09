import matplotlib.pyplot as plt
import csv
import argparse

plt.rcParams.update({"font.family": "serif", "font.size": 10})

parser = argparse.ArgumentParser(description="plot results from a ")
parser.add_argument("files", type=str, help="file containing list of data files")
parser.add_argument("output", type=str, help="file to save the plot")
parser.add_argument("-mark", action="store_true", help="use markers")
args = parser.parse_args()

with open(args.files, "r") as f:
    files = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["file"][density] = average_time
results: dict[str, dict[str, dict[float, float]]] = {}

for file in files:
    results[file] = {}
    results[file]["R2U2 (C)"] = {}
    results[file]["R2U2 (Rust)"] = {}
    results[file]["Hydra"] = {}
    results[file]["SABRe"] = {}
    results[file]["SABRe (Decomposed)"] = {}
    with open(file, newline="") as csvfile:
        reader = csv.reader(csvfile)
        next(reader) # skip header
        for row in reader:
            density = float(row[0])
            results[file]["R2U2 (C)"][density] = float(row[1]) / 1_000_000
            results[file]["R2U2 (Rust)"][density] = float(row[2]) / 1_000_000
            results[file]["Hydra"][density] = float(row[3]) / 1_000_000
            results[file]["SABRe"][density] = float(row[4]) / 1_000_000
            results[file]["SABRe (Decomposed)"][density] = float(row[5]) / 1_000_000

fig, ax = plt.subplots(layout="tight", figsize=(6,3))

for file in results.keys():
    color = ""
    linewidth = 1

    linestyle = "solid"
    if "10000" in file:
        linestyle = "dotted"
        marker = "o"
    elif "1024" in file:
        linestyle = "dashed"
        marker = "s"
    elif "5000" in file:
        linestyle = "dashdot"
        marker = "h"
    else:
        linestyle = "solid"
        marker = "^"

    for tool in results[file].keys():
        if tool == "R2U2 (C)":
            color = "red" 
        elif tool == "R2U2 (Rust)":
            color = "firebrick" 
        elif tool == "Hydra": 
            color = "blue"    
        elif tool == "SABRe":
            color = "darkorchid" 
        elif tool == "SABRe (Decomposed)":
            color = "lime"

        ax.plot(
            list(results[file][tool].keys()), 
            list(results[file][tool].values()), 
            color=color, linewidth=linewidth, linestyle=linestyle,
            marker=marker, markersize=5
        )

ax.set_xscale("log")
plt.grid(axis="y")
plt.xlabel("Trace Density")
plt.ylabel("Throughput ($10^6$ verdicts/s)")
plt.savefig(args.output, dpi=300)
