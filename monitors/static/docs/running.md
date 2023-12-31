# Running

These instructions are for using the provided R2U2 CLI example; to use R2U2 as a library, see [embedding R2U2](./embedding.md).

## Prerequisites

1. [Build](./building.md) the regular (`bin`) or debug (`debug`) Makefile targets
2. Construct a specification binary using C2P0

## With a Signal File

From the `monitors/static` directory execute:
```bash
./build/r2u2{_debug} ./path/to/specification.bin ./path/to/signals.csv
```
That is, run either `./build/r2u2` for release or `./build/r2u2_debug` for development versions of R2U2, and provide relative or absolute paths to the specification binary and signal files.

The format for the signal files can be found in the [file formats reference](#signal_trace_files).

The output will be streamed to the screen by default by can be saved to files with standard shell redirection, see [output](./output.md) for more details.

## Using External Signal Sources

From the `monitors/static` directory execute:
```bash
./build/r2u2{_debug} ./path/to/specification.bin
```
That is, run either `./build/r2u2` for release or `./build/r2u2_debug` for development versions of R2U2 and provide relative or absolute path to the specification binary.

At this point, R2U2 will wait for comma-separated, newline delineated input of the next signal values on standard in.
Be default this will be via the keyboard, allowed users to enter input by hand such as "1,1,0,3.14" and see the output of the next round of evaluation after hitting enter.

Since this mode reads form standard in, it can also be fed data via pipe or file redirect like any standard Unix CLI.

The output will be streamed to the screen by default by can be saved to files with standard shell redirection, see [output](./output.md) for more details.
