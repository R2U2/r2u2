import matplotlib.pyplot as plt
import csv
import argparse

plt.rcParams.update({"font.family": "serif", "font.size": 10})

parser = argparse.ArgumentParser(description="plot results")
parser.add_argument("files", type=str, help="file containing list of data files")
parser.add_argument("output", type=str, help="file to save the plot")
args = parser.parse_args()

with open(args.files, "r") as f:
    files = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["spec"]["tool"] = time
results: dict[str, dict[str, float]] = {}

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
            if tool == "sabre":
                tool = "SABRe"
            elif tool == "hydra":
                tool = "Hydra"
            elif tool == "r2u2_c":
                tool = "R2U2 (C)"
            elif tool == "r2u2_rust":
                tool = "R2U2 (Rust)"
            
            if spec not in results:
                results[spec] = {}
            if tool not in results[spec]:
                results[spec][tool] = 0

            results[spec][tool] = float(row[1]) / 1_000_000

fig, ax = plt.subplots(layout="tight", figsize=(6,3))

# Prepare data for the bar graph
specs = ["Future", "Until", "Min Duration", "Between", "Prec Chain"]
tools = ["SABRe", "Hydra", "R2U2 (C)", "R2U2 (Rust)"]
bar_width = 0.25
group_spacing = 0.3  # Add extra spacing between groups
x = [i * (1 + group_spacing) for i in range(len(specs))]  # Add spacing between groups

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
        [results[spec].get(tool, 0) for spec in specs],
        width=bar_width,
        label=tool,
        color=(
            "red" if tool == "R2U2 (C)" else
            "firebrick" if tool == "R2U2 (Rust)" else
            "blue" if tool == "Hydra" else
            "darkorchid" if tool == "SABRe" else
            "gray"  # Default color for any other tool
        )
    )

# Set x-axis labels and legend
ax.set_xticks([i + (len(tools) - 1) * bar_width / 2 for i in x])  # Center labels under groups
ax.set_xticklabels(specs)

# Add labels and title
plt.ylabel("Throughput (10^6 verdicts/s)")
plt.grid(axis="y")
plt.tight_layout()

# Save the plot
plt.savefig(args.output, dpi=100)
