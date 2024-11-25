# R2U2 Static Monitor (C Version)

## Dependencies:
- C99 std compiler (gcc or clang)
- Make

## Compiling

Run `make` to generate the binary and static library in `build/`. See `make help` for all available
build targets.

## Running

After obtaining a specification binary via C2PO (see top-level README.md), run

    ./build/r2u2 path/to/spec.bin path/to/trace.csv

to run R2U2 over a simulated trace. Alternatively, R2U2 will accept input from `stdin` when no trace
file is given:

    ./build/r2u2 path/to/spec.bin < path/to/trace.csv
