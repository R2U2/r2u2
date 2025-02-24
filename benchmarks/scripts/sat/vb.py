import csv
import argparse

parser = argparse.ArgumentParser(description="Compute virtual best for a set of benchmarks")
parser.add_argument("benchmarks", type=str, help="File containing list of benchmarks")
parser.add_argument("output", type=str, help="File to save the data")
args = parser.parse_args()

with open(args.benchmarks, "r") as f:
    benchmarks = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["benchmarkname"]["testname"] = ("result", "time")
results: dict[str, dict[str, tuple[float, list[str], str]]] = {}
results["vb"] = {}

# CSV files are of the form:
# "testname", "status", "encoding-time", "sat-result", "sat-time", "calls"
for benchmark in benchmarks:
    results[benchmark] = {}
    with open(benchmark, newline="") as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            testname = row[0]
            if row[3] == "sat" or row[3] == "unsat":
                results[benchmark][testname] = (float(row[4]), row, benchmark)
                if testname in results["vb"]:
                    results["vb"][testname] = min(
                        results["vb"][testname], (float(row[4]), row, benchmark)
                    )
                else:
                    results["vb"][testname] = (float(row[4]), row, benchmark)
            elif testname not in results["vb"]:
                results["vb"][testname] = (float("inf"), row, "None")


with open(args.output, "w") as f:
    for testname, (result, row, benchmark) in results["vb"].items():
        f.write(f"{testname},{result},{row[2]},{row[3]},{row[4]},{row[5]},{benchmark}\n")

