import sys

if len(sys.argv) != 4:
    print(f"usage: python3 {sys.argv[0]} <r2u2-output-file> <hydra-output-file> <bvmon-output-file>")
    exit(1)

r2u2_filename = sys.argv[1]
hydra_filename = sys.argv[2]
bvmon_filename = sys.argv[3]

r2u2_trace: list[bool] = []
hydra_trace: list[bool] = []
bvmon_trace: list[bool] = []

# For the following, assume we have the following reference trace of length 16 for the examples:
# [T, T, T, T, F, F, F, F, F, F, F, F, T, T, T, T]
# This trace states the formula holds from times 0-3, fails from 4-11, and holds again from 12-15.

# R2U2 output format:
# FID ':' TS ',' ('F' | 'F') 
# where FID and TS are natural numbers wth FID being a formula ID and TS being the timestamp. 
# We assume a single formula per run, so FID will always be 0.
# Example:
# 0:2,T
# 0:4,F
# 0:11,F
# 0:12,T
with open(r2u2_filename, "r") as f:
    content = f.read()

cur_ts = 0
for line in content.split("\n"):
    if line == "":
        continue
    ts, verdict = line.split(":")[1].split(",")
    while cur_ts <= int(ts):
        r2u2_trace.append(verdict == "T")
        cur_ts += 1

# Hydra output format:
# TS ':' OFFSET ' ' ('true' | 'false')
# where TS and OFFSET are natural numbers wth TS being the timestamp. 
# OFFSET is used when multiple verdicts come in for a timestamp at differing lines of the log, 
# but we do not consider this case so OFFSET will always be 0.
# (Example: @0 a0 @0 a1 ... --- this is not allowed)
# Example: 
# 2:0 true
# 11:0 false
# 12:0 true
with open(hydra_filename, "r") as f:
    content = f.read()

cur_ts = 0
for line in content.split("\n"):
    if line == "":
        continue
    ts = line.split(":")[0]
    verdict = line.split(" ")[1]
    while cur_ts <= int(ts):
        hydra_trace.append(verdict == "true")
        cur_ts += 1

# bvmon output format:
# \x*
# where \x is a hexadecimal digit.
# Each bit of the sequence of hex digits represent the verdict at that time.
# Example:
# E00F
# (in binary: 111000000001111)
with open(bvmon_filename, "r") as f:
    content = f.read()

for hex_digit in content:
    bvmon_trace.extend([bit == "1" for bit in f"{int(hex_digit, 16):04b}"])

# print(f"R2U2 trace: {r2u2_trace}")
# print(f"Hydra trace: {hydra_trace}")
# print(f"BvMon trace: {bvmon_trace}")

for i in range(min(len(r2u2_trace), len(hydra_trace), len(bvmon_trace))):
    r2u2 = r2u2_trace[i]
    hydra = hydra_trace[i]
    bvmon = bvmon_trace[i]
    if r2u2 != hydra or r2u2 != bvmon or hydra != bvmon:
        print(f"Discrepancy at timestamp {i}: R2U2={r2u2}, Hydra={hydra}, BvMon={bvmon}")
