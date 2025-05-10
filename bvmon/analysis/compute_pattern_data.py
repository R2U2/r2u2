import csv
import argparse

parser = argparse.ArgumentParser(description="compute average throughput speedup and memory usage")
parser.add_argument("files", type=str, help="file containing list of data files")
args = parser.parse_args()

with open(args.files, "r") as f:
    files = [b.strip("\n") for b in f.readlines()]

# results["spec"]["tool"] = throughput, memory
results: dict[str, dict[str, tuple[float, float]]] = {}

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
                spec = "Global Between" 
            elif "min_duration" in file:
                spec = "Min Duration"
            elif "prec_chain" in file:
                spec = "Prec Chain"
            elif "until" in file:
                spec = "Until"

            tool = row[0]
            if spec not in results:
                results[spec] = {}
            if tool not in results[spec]:
                results[spec][tool] = (0.0, 0.0)

            results[spec][tool] = float(row[1]), float(row[2])  # Store throughput and memory

# Compute how many times faster "bvmon" is than the fastest of "R2U2 C" and "R2U2 Rust" in terms of throughput
# Also compute average times faster over all specs
avg_times_faster_r2u2 = 0
avg_times_faster_hydra = 0
avg_mem_r2u2 = 0
avg_mem_hydra = 0
avg_mem_bvmon = 0
n = 0
for spec in results.keys():
    if "bvmon" not in results[spec]:
        continue
    bvmon_tp = results[spec]["bvmon"][0]
    r2u2_tp = results[spec]["r2u2_c"][0]
    hydra_tp = results[spec]["hydra"][0]
    times_faster_r2u2 = bvmon_tp / r2u2_tp
    times_faster_hydra = bvmon_tp / hydra_tp
    avg_times_faster_r2u2 += times_faster_r2u2
    avg_times_faster_hydra += times_faster_hydra

    avg_mem_r2u2 += results[spec]["r2u2_c"][1] / 1024
    avg_mem_hydra += results[spec]["hydra"][1] / 1024
    avg_mem_bvmon += results[spec]["bvmon"][1] / 1024
    n += 1

avg_times_faster_r2u2 /= n
avg_times_faster_hydra /= n
avg_mem_r2u2 /= n
avg_mem_hydra /= n
avg_mem_bvmon /= n

print(f"bvmon avg times thruput (r2u2): {avg_times_faster_r2u2:.2f}x")
print(f"bvmon avg times thruput (hydra): {avg_times_faster_hydra:.2f}x")
print(f"r2u2 avg mem: {avg_mem_r2u2:.2f} MB")
print(f"hydra avg mem: {avg_mem_hydra:.2f} MB")
print(f"bvmon avg mem: {avg_mem_bvmon:.2f} MB")
