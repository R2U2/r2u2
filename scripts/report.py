import pathlib
import csv
import itertools

CURDIR = pathlib.Path(__file__).parent

# this dict will be of the form:
# results["benchmarkname"]["testname"] = "result"
results: dict[str, dict[str, str]] = {}

# CSV files are of the form:
# "filename", "status", "result", "time", "calls"
for file in CURDIR.glob("*.csv"):
    benchmark_name = file.stem
    results[benchmark_name] = {}
    with open(file, newline="") as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            testpath = pathlib.Path(row[0])
            testname = testpath.stem

            if testname in results[benchmark_name]:
                print(f"Duplicate test {testname} in benchmark {benchmark_name}")

            results[benchmark_name][testname] = row[3]

benchmarks = sorted(list(results.keys()))
tests = list(results[benchmarks[0]].keys())

# report number of failures in each benchmark
print("Failures:")
for benchmark in benchmarks:
    failures = sum([1 for test in tests if test in results[benchmark] and results[benchmark][test] == "fail"])
    print(f"{benchmark:31}: {failures}")

benchmark_sizes = [len(results[benchmark]) for benchmark in benchmarks]
if any(size != benchmark_sizes[0] for size in benchmark_sizes):
    print("\nDifferent number of tests in each benchmark")
    print("\n".join([f"{benchmark:31}: {len(results[benchmark])}" for benchmark in benchmarks]))
    exit(1)

# # this will store "filename" -> list of results for all files if there are any disagreements
# disagreements = {}

# # now we can iterate over the results see if there are any diagreements
# for b1,b2 in itertools.combinations(results.values(), 2):
#     for test in tests:
#         if (
#             (
#                 (results[b1[test]] == "sat" and results[b2][test] == "unsat") or 
#                 (results[b1[test]] == "unsat" and results[b2][test] == "sat") 
#             ) and test not in disagreements
#         ):
#             disagreements[test] = [b["test"] for b in benchmarks]

# if len(disagreements) == 0:
#     print("No disagreements")
# else:
#     print("Disagreements:")
#     print("\n".join(disagreements))
