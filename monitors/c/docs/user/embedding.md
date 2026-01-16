# Embedding

When using R2U2 as a library within a user-provided application, configuration and execution of the monitor becomes the callers responsibility.
The provided `cli/main.c` that defines the R2U2 CLI also serves as a reference implementation and can be treated as an example of library use.

## Reserving Memory

The "static" in the name "R2U2 static monitor" refers to the monitor not perform any memory allocation calls, it is the user's responsibility to preallocate the required memory in arenas and array used by the monitor.
With careful programming, this can even be done such that the monitor memory itself is encoded in the .bss segment of the application and therefore take (virtually)no space on disk until loaded.

A `r2u2_monitor_t` struct is used to represent the state and memory of an instance of R2U2.
The `R2U2_DEFAULT_MONITOR` macro will setup a monitor with default extents, see [configuration](./configuration.md) to adjust those sizes.
Alternatively, the required memory can be set aside by the user and referenced by the monitor struct, allowing arbitrary sizes of all memory arenas and arrays to be built even at runtime.

## C2PO Specification Input
Each R2U2 static monitor monitors its own specifications that have been specified utilizing C2PO. It is the user's responsibility to set the C2PO binary correctly. The specification binary must be passed as a uint8_t array memory
to `r2u2_load_specification` as defined in `r2u2.h`.

:::{note}
The `xxd -i [file path to C2PO binary]` terminal command will dump the binary compiled by C2PO into a byte array.
:::

## Signal Input

System state values, called signals, are read from the signal vector by the monitor on each step.
It is the user's responsibility to set these values correctly using the `load_bool_signal`, `load_float_signal`, `load_int_signal`, and `load_string_signal` functions. The signal vector itself is an array on integers/floats/booleans. 

In the CLI, the r2u2_csv_reader_t is used to read signal values and load them into the monitor's signal vector.
Consult `cli/csv_trace.c` for an example of loading the signal vector.

## Verdict Output

Verdict output is written to the `out_file` file pointer if set and the `out_func` callback, again if set, is fired with the result of the evaluation.
See [](./output.md) for more details.

## Initializing and Running the Monitor

As demonstrated in `cli/main.c`, a standard life-cycle for an R2U2 monitor is:

1. A monitor must be first defined (e.g., `r2u2_monitor_t monitor = R2U2_DEFAULT_MONITOR;`). The specifications can loaded or even later updated with `r2u2_load_specification`; this will also reset the monitor to its intial state.
2. The output file pointer is set
3. Signals must be loaded in according to the mapping specified when compiling the specification file through `load_bool_signal`, `load_float_signal`, `load_int_signal`, and `load_string_signal`.
4. `r2u2_step` is called to run the monitor for a single time step
5. Error conditions are checked
6. The signal vector is updated if a time-step has completed
7. Loop back to step 4 and continue executing until monitoring is complete


## Platform Constraints and Compatibility

While the monitor itself is carefully constructed to ensure internal consistency, the primary source of incompatibility is the assumptions of monitor configuration made by C2PO when packaging the specification binary.
Pay careful attention to configuration flags in C2PO used to inform the assembler of the monitor setup.
