# Memory Controllers

Memory controllers define structures and functions representing higher-level data types used by engines during execution.

## Monitor
The monitor structure defined here tracks the monitor internal state and stores all the relevant information used by R2U2 during execution.

There are 4  major types of fields in the monitor structure:
1. The vector clock, made up of the time stamp, BZ and TL program counters, and progress indicator.
2. Instruction memory, including an instruction table for both BZ and TL instructions and auxiliary string information.
3. Internal memory such as input signal buffer, atomic proposition buffer, and SCQ memory arena.
4. Output buffers made of arrays containing the verdict stream and contract information including and index referring to the length of valid buffered information for the given time stamp

## Shared Connection Queue
The primary working memory of the temporal engine, shared connection queues are many-reader, single-writer, circular buffers.

The SCQ memory arena consists of two arrays. The first holding control metadata information for each SCQ (e.g., lower bound, upper bound, scq location, etc.),
and the second consisting of all SCQ slots (which each SCQ reserves a portion by setting the appropriate control metadata).

:::{note}
If the SCQ memory domain is insufficient, Rust will panic.
:::

For SCQ operational semantics and sizing, see {footcite:p}`AJR2025` and {footcite:p}`KZJZR20`.

---

:::{footbibliography}
:::
