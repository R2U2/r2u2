# Embedding

When using R2U2 as a library within a user-provided application, configuration and execution of the monitor becomes the callers responsibility.
The provided `main.c` that defines the R2U2 CLI also serves as a reference implementation and can be treated as an example of library use.

## Reserving Memory

The "static" in the name "R2U2 static monitor" refers to the monitor not perform any memory allocation calls, it is the user's responsibility to preallocate the required memory in arenas and array used by the monitor.
With careful programming, this can even be done such that the monitor memory itself is encoded in the .bss segment of the application and therefore take (virtually)no space on disk until loaded.

A `r2u2_monitor_t` struct is used to represent the state and memory of an instance of R2U2.
The `R2U2_DEFAULT_MONITOR` macro will setup a monitor with default extents, see [configuration](./configuration.md) to adjust those sizes.
Alternatively, the required memory can be set aside by the user and referenced by the monitor struct, allowing arbitrary sizes of all memory arenas and arrays to be built even at runtime.

## Signal Input

System state values, called signals, are read from the signal vector by the monitor on each tic.
It is the user's responsibility to set these values correctly.

The signal vector itself is an array of pointers to (null-terminated) strings representing the signal values.
Values are provided as strings to allow for type-casting of values by the front-end, for example changing the floating point type or reading a 1 or 0 as a boolean.

In the R2U2 CLI, the CSV helper is used to read signal values and load them into the monitor's signal vector.
Consult `memory/csv_trace.c` for an example of loading the signal vector.

## Verdict Output

Verdict output is written to the `out_file` file pointer if set and the `out_func` callback, again if set, is fired with the result of the evaluation.
See [](./output.md) for more details.

## Initializing and Running the Monitor

As demonstrated in `main.c`, a standard life-cycle for an R2U2 monitor is:

1. The instruction memory is loaded by copying or `mmap`-ing the specification binary
2. `r2u2_init` is called which resets the monitor (logical) clock and prepossesses the instructions
3. The output file pointer is set
4. The signal vector state is loaded
5. An execution function is called to run the monitor, which can be one of the following:
    - `r2u2_step` executes a single R2U2 instruction. Good for cooperative multitasking
    - `r2u2_spin` after the first spin, all signal values are latched but the time-step might not be complete. Most time-steps require two spins
    - `r2u2_tic` runs until one time-step is complete. Default for most cases as it provides all verdicts available with current knowledge and ends when the signal vector should be refreshed
    - `r2u2_run` runs continuously, requires external refreshing of the signal vectors such as DMA or memory-mapped registers
6. Error conditions are checked
7. The signal vector is updated if a time-step has completed
8. Loop back to step 5 and continue executing until monitoring is complete

## Platform Constraints and Compatibility

While the monitor itself is carefully constructed to ensure internal consistency, the primary source of incompatibility is the assumptions of monitor configuration made by C2PO when packaging the specification binary.
Pay careful attention to configuration flags in C2PO used to inform the assembler of the monitor setup.

The easiest way to ensure compatibility is to run the C2PO formula compiler on the same platform as you build and run R2U2, but if that isn't possible and you suspect platform compatibility issues, compare the decoded instructions in the R2U2 debug logging to the assembly output of C2PO.
