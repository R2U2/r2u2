# Embedding

When using R2U2 as a library within a user-provided application, configuration and execution of the monitor becomes the callers responsibility.
The `r2u2_core` crate is written in `no_std` and includes the core of R2U2 with specified API calls. Both `r2u2_cli` and 
`r2u2_cortex_m_example` demonstrate examples of how to utilize the `r2u2_core` crate. `r2u2_cli` allows users
to utilize R2U2 through a commandline interface, and `r2u2_cortex_m_example` demonstrates how to embed R2U2 on a microcontroller.

- `r2u2_core` is available as a publically accessibly crate here for easy import into applications: [https://crates.io/crates/r2u2_core](https://crates.io/crates/r2u2_core)
- Documentation on `r2u2_core` is available here: [https://docs.rs/r2u2_core/latest/r2u2_core/](https://docs.rs/r2u2_core/latest/r2u2_core/)

## Reserving Memory

The "static" in the name "R2U2 static monitor" refers to the monitor not perform any memory allocation calls, it is the user's responsibility to provide proper sizing parameters. A `Monitor` struct is used to represent the state and memory of an instance of R2U2. The `get_monitor` function will setup a monitor with default extents, see [configuration](./configuration.md) to adjust those sizes.

## C2PO Specification Input
Each R2U2 static monitor monitors its own specifications that have been specified utilizing C2PO. It is the user's responsibility to set the C2PO binary correctly. The specification binary can be passed by reference as `&[u8]` when creating the monitor with `get_monitor` or updated with `update_binary_file`.

:::{note}
The `xxd -i [file path to C2PO binary]` terminal command will dump the binary compiled by C2PO into a byte array.
:::

## Signal Input

System state values, called signals, are read from the signal vector by the monitor on each step.
It is the user's responsibility to set these values correctly using the `load_bool_signal`, `load_float_signal`, `load_int_signal`, and `load_string_signal` functions. The signal vector itself is an array on integers/floats/booleans. 

In the R2U2 CLI, the CSV helper is used to read signal values and load them into the monitor's signal vector.
Consult `r2u2_cli/src/main.rs` for an example of loading the signal vector.

## Verdict Output

Verdict output is accessible via the `get_output_buffer` and `get_contract_buffer` functions.
See [](./output.md) for more details.

## Initializing and Running the Monitor

As demonstrated in `r2u2_cli/src/main.rs`, a standard life-cycle for an R2U2 monitor is:

1. A monitor must be created utilizing `get_monitor`. The specification file from C2PO must be passed by reference as `&[u8]`. The specifications can later be updated with `update_binary_file`; this will also reset the monitor to its intial state.
2. Signals must be loaded in according to the mapping specified when compiling the specification file through `load_bool_signal`, `load_float_signal`, `load_int_signal`, and `load_string_signal`.
3. Run the monitor for a single timestep with `monitor_step`.
4. Get output data through `get_output_buffer` and `get_contract_buffer`.
5. Repeat steps 2-4. (Optionally check for overflow with the output of `monitor_step` or `get_overflow_error`.)
