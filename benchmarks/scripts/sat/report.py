import pathlib
import csv
import itertools
import pprint

CURDIR = pathlib.Path(__file__).parent

# this dict will be of the form:
# results["benchmarkname"]["testname"] = ("c2po_status", "result", "time")
results: dict[str, dict[str, tuple[str, str, str]]] = {}

# CSV files are of the form:
# "filename", "status", "result", "time", "calls"
for file in (CURDIR / "results").glob("*.csv"):
    benchmark_name = file.stem
    results[benchmark_name] = {}
    with open(file, newline="") as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            testpath = pathlib.Path(row[0])
            testname = testpath.stem
            results[benchmark_name][testname] = (row[1], row[3], row[4])

benchmarks = sorted(list(results.keys()))

# report number of c2po errors in each benchmark
print("C2PO Errors:")
for benchmark in benchmarks:
    tests = results[benchmark].keys()
    failures = sum([1 for test in tests if test in results[benchmark] and results[benchmark][test][0] == "err"])
    print(f"{benchmark:31}: {failures}")
print()

# report number of failures in each benchmark
print("Failures:")
for benchmark in benchmarks:
    tests = results[benchmark].keys()
    failures = sum([1 for test in tests if test in results[benchmark] and results[benchmark][test][1] == "fail"])
    print(f"{benchmark:31}: {failures}")
print()

benchmark_sizes = [len(results[benchmark]) for benchmark in benchmarks]
CORRECT_SIZE = 1_000
if any(size != benchmark_sizes[0] for size in benchmark_sizes):
    print("\nDifferent number of tests in each benchmark")
    print("\n".join([f"{benchmark:31}: {len(results[benchmark])}" for benchmark in benchmarks]))
    for i in range(len(benchmarks)):
        benchmark = benchmarks[i]
        if len(results[benchmark]) != CORRECT_SIZE:
            print(f"Removing {benchmark}")
            del results[benchmark]

# update benchmarks after removing any
benchmarks = sorted(list(results.keys()))

# this will store "filename" -> list of results for all files if there are any disagreements
disagreements = {}

# now we can iterate over the results see if there are any diagreements
for b1,b2 in itertools.combinations(results.values(), 2):
    tests = set(b1.keys()) | set(b2.keys())
    for test in tests:
        if test not in b1 or test not in b2:
            continue
        if (
            (
                (b1[test][1] == "sat" and b2[test][1] == "unsat") or
                (b1[test][1] == "unsat" and b2[test][1] == "sat")
            ) and test not in disagreements
        ):
            disagreements[test] = [(b, results[b][test]) for b in benchmarks if test in results[b]]

if len(disagreements) == 0:
    print("No disagreements")
else:
    print("Disagreements:")
    pprint.pprint(disagreements)

