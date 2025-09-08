# Memory Controllers

Memory controllers define structures and functions representing higher-level data types used by engines during execution.

## Contract Status
Contract status allows the use of the `=>` operator in C2PO along with the `R2U2_TL_Contract_Status` feature flag to enable a tri-state output of assume-guarantee contracts.
During formula compilation, each AGC is broken into three MLTL formulas, one for each state - inactive, verified, or violated.
This forms a "one-hot" encoding where the truth value of each formula corresponds to one of the three states.

:::{note} Three formula in a one-hot encoding is used instead of two formulas (since 2 bits can encode 4 states) so that verdicts would not need to be cached for comparison. If one verdict stream runs ahead of another, all returns are still valid contract status without waiting for additional information to be ready for comparison.
:::

The `r2u2_contract_status_reporter_t` provides the memory backing for the additional contact storage while `r2u2_contract_status_load_mapping` configures the struct based on information from the auxiliary section of the specification binary.
Then, `r2u2_contract_status_report` is used to check if newly produced verdicts also correspond to a contract status.

The contract status reporter tracks which three formulas constitute the AGC as well as the name of the contract for output.

## CSV Trace
The `r2u2_csv_reader_t` struct and associated `r2u2_csv_load_next_signals` function provides a basic parser for the CSV signal trace file format (see References for details) and is used by `main.c` to parse, buffer, and load CSV inputs to the signal vector.

## Monitor
The monitor structure defined here tracks the monitor internal state and stores the pointers to all the memory used by R2U2 during execution.

There are 4  major types of fields in the monitor structure:
1. The vector clock, made up of the time stamp, program counter, and progress indicator.
2. Instruction memory, including a pointer to the raw data, and a pointer to a table filled during instantiation which allows constant time access to the variable-width instruction memory.
3. Output pointers, defining how to return produced verdicts.
4. Memory domain pointers, point to arrays or arenas of memory defined by the memory controllers and manipulated by the engines.

The macro `R2U2_DEFAULT_MONITOR` is also defined here which provides a .bss friendly instantiation of a monitor.

## Shared Connection Queue
The primary working memory of the future-time temporal engine, shared connection queues are many-reader, single-writer, circular buffers.

SCQs are laid out in memory following a stack/heap pattern within the fixed-extent domain.
Each SCQ created by a TL configuration instruction creates a fixed-size metadata segment that is appended to the previous one starting at the beginning of the memory domain, and a number of queue slots representing the actual circular buffer are reserved counting up from the end of the domain.

This arrangement allows for either a few very large buffers or many small buffers to utilize the same arena instead of bounding the number and size of queues separately.

If the SCQ memory domain is insufficient, the metadata "stack" will crash into the queue slot "heap" in the middle of the domain, but this is caught during initialization when DEBUG memory checks are enabled.

For SCQ operational semantics and sizing, see {footcite:p}`AJR2025` and {footcite:p}`KZJZR20`.

---

:::{footbibliography}
:::
