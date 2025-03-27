import csv
import argparse
import pprint
import sys

parser = argparse.ArgumentParser(description="compute virtual best for a set of benchmarks")
parser.add_argument("benchmarks", type=str, help="file containing list of benchmarks")
parser.add_argument("output", type=str, help="file to save the data")
parser.add_argument("-data", action="store_true", help="output extra data")
args = parser.parse_args()

with open(args.benchmarks, "r") as f:
    benchmarks = [b.strip("\n") for b in f.readlines()]

# this dict will be of the form:
# results["benchmark"]["test"] = ("result", time)
results: dict[str, dict[str, tuple[float, list[str], str]]] = {}
results["vb"] = {}

# data["benchmark"] = (# solved, # sat, # unsat, # vb, # unique)
data: dict[str, dict[str, int]] = {}

# CSV files are of the form:
# "test", "status", "encoding-time", "sat-result", "sat-time", "calls"
for benchmark in benchmarks:
    results[benchmark] = {}
    data[benchmark] = {"solved": 0, "sat": 0, "unsat": 0, "vb": 0, "unique": 0 }
    with open(benchmark, newline="") as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            testname = row[0]
            if row[3] == "sat" or row[3] == "unsat":
                results[benchmark][testname] = (float(row[4]), row, benchmark)
                if testname in results["vb"]:
                    vb_time = min(
                        results["vb"][testname], (float(row[4]), row, benchmark)
                    )
                    results["vb"][testname] = vb_time
                else:
                    results["vb"][testname] = (float(row[4]), row, benchmark)

                data[benchmark]["solved"] += 1
                data[benchmark]["sat"] += 1 if row[3] == "sat" else 0
                data[benchmark]["unsat"] += 1 if row[3] == "unsat" else 0
            elif testname not in results["vb"]:
                results[benchmark][testname] = (float("inf"), row, benchmark)
                results["vb"][testname] = (float("inf"), row, "None")
            else:
                results[benchmark][testname] = (float("inf"), row, benchmark)

for benchmark,res in results.items():
    if benchmark == "vb":
        continue

    for test in [test for test in res.keys() if results["vb"][test][2] == benchmark]:
        data[benchmark]["vb"] += 1

    for test in [
        test
        for test in res.keys()
        if all(
            [
                "sat" not in results[b][test][1][3]
                for b in results.keys()
                if b != benchmark and b != "vb"
            ]
        )
        if "sat" in results[benchmark][test][1][3]
    ]:
        data[benchmark]["unique"] += 1

with open(args.output, "w") as f:
    for testname, (result, row, benchmark) in results["vb"].items():
        f.write(f"{testname},{result},{row[2]},{row[3]},{row[4]},{row[5]},{benchmark}\n")

if args.data:
    pprint.pprint(data)