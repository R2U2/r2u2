import csv
import argparse

parser = argparse.ArgumentParser(description="compute percent difference in throughput")
parser.add_argument("files", type=str, help="file containing list of data files")
args = parser.parse_args()

with open(args.files, "r") as f:
    files = [b.strip("\n") for b in f.readlines()]

# results["density"]["tool"] = throughput
results: dict[str, dict[float, dict[str, float]]] = {}

for file in files:
    results[file] = {}
    with open(file, newline="") as csvfile:
        reader = csv.reader(csvfile)
        reader.__next__()  # skip header
        for row in reader:
            density = float(row[0])
            r2u2_throughput = float(row[1])
            hydra_throughput = float(row[2])
            sabre_throughput = float(row[3])
            sabre_decomposed_throughput = float(row[4])
            if density not in results:
                results[file][density] = {}
            results[file][density]["r2u2"] = r2u2_throughput
            results[file][density]["hydra"] = hydra_throughput
            results[file][density]["sabre"] = sabre_throughput
            results[file][density]["sabre_decomposed"] = sabre_decomposed_throughput

max_percent_diffs = {}
for file in results:
    max_r2u2_throughput = max([results[file][density]["r2u2"] for density in results[file]])
    max_hydra_throughput = max([results[file][density]["hydra"] for density in results[file]])
    max_sabre_throughput = max([results[file][density]["sabre"] for density in results[file]])
    max_sabre_decomposed_throughput = max([results[file][density]["sabre_decomposed"] for density in results[file]])

    min_r2u2_throughput = min([results[file][density]["r2u2"] for density in results[file]])
    min_hydra_throughput = min([results[file][density]["hydra"] for density in results[file]])
    min_sabre_throughput = min([results[file][density]["sabre"] for density in results[file]])
    min_sabre_decomposed_throughput = min([results[file][density]["sabre_decomposed"] for density in results[file]])

    max_percent_diffs[file] = {}
    max_percent_diffs[file]["r2u2"] = (max_r2u2_throughput - min_r2u2_throughput) / max_r2u2_throughput * 100
    max_percent_diffs[file]["hydra"] = (max_hydra_throughput - min_hydra_throughput) / max_hydra_throughput * 100
    max_percent_diffs[file]["sabre"] = (max_sabre_throughput - min_sabre_throughput) / max_sabre_throughput * 100
    max_percent_diffs[file]["sabre_decomposed"] = (max_sabre_decomposed_throughput - min_sabre_decomposed_throughput) / max_sabre_decomposed_throughput * 100
    
# Print the results
for file in max_percent_diffs:
    print(f"File: {file}")
    print(f"Max percent difference for r2u2: {max_percent_diffs[file]['r2u2']:.2f}%")
    print(f"Max percent difference for hydra: {max_percent_diffs[file]['hydra']:.2f}%")
    print(f"Max percent difference for sabre: {max_percent_diffs[file]['sabre']:.2f}%")
    print(f"Max percent difference for sabre decomposed: {max_percent_diffs[file]['sabre_decomposed']:.2f}%")