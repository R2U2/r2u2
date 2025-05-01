import matplotlib.pyplot as plt
import csv
import argparse

plt.rcParams.update({"font.family": "serif", "font.size": 10})

parser = argparse.ArgumentParser(description="plot results from a ")
parser.add_argument("files", type=str, help="file containing list of data files")
parser.add_argument("output", type=str, help="file to save the plot")
args = parser.parse_args()

with open(args.files, "r") as f:
    files = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["spec"]["tool"] = memory list
results: dict[str, dict[str, list[float]]] = {}

for file in files:
    results[file] = {}
    with open(file, newline="") as csvfile:
        reader = csv.reader(csvfile)
        next(reader) # skip header
        for row in reader:
            spec = ""
            if "future" in file:
                spec = "Future"
            elif "global_btwn_q_r" in file:
                spec = "Between" 
            elif "min_duration" in file:
                spec = "Min Duration"
            elif "prec_chain" in file:
                spec = "Prec Chain"
            elif "until" in file:
                spec = "Until"

            tool = row[0]
            if "bvmon" in tool:
                tool = "bvmon"
            elif "hydra" in tool:
                tool = "hydra"
            elif "r2u2_c" in tool:
                tool = "r2u2"
            
            if spec not in results:
                results[spec] = {}
            if tool not in results[spec]:
                results[spec][tool] = []

            results[spec][tool].append(float(row[2]) / 1024) # convert to MB

fig, ax = plt.subplots(layout="tight", figsize=(6,3))

# Calculate averages for each specification and tool
averages = {
    spec: {tool: sum(times) / len(times) for tool, times in tools.items()}
    for spec, tools in results.items()
}

# Prepare data for the bar graph
specs = ["Future", "Until", "Min Duration", "Between", "Prec Chain"]
tools = ["bvmon", "hydra", "r2u2"]
bar_width = 0.25
x = range(len(specs))

# Create bar positions for each tool
positions = {
    tool: [i + idx * bar_width for i in x]
    for idx, tool in enumerate(tools)
}

# Plot the bar graph
fig, ax = plt.subplots(layout="tight", figsize=(6, 3))
for tool in tools:
    ax.bar(
        positions[tool],
        [averages[spec].get(tool, 0) for spec in specs],
        width=bar_width,
        label=tool,
        color=(
            "red" if tool == "r2u2" else
            "blue" if tool == "hydra" else
            "darkorchid" if tool == "bvmon" else
            "gray"  # Default color for any other tool
        )
    )

# Set x-axis labels and legend
ax.set_xticks([i + bar_width for i in x])
ax.set_xticklabels(specs)
# plt.xticks(rotation=12)
# ax.legend(loc="upper right")

# Add labels and title
plt.ylabel("Avg Max RSS (MB)")
plt.grid(axis="y")
plt.tight_layout()

# Save the plot
plt.savefig(args.output, dpi=100)
