# Execution Engines

Each engine is identified by a tag value in the `r2u2_engine_tag_t` enum:

```C
typedef enum {
    R2U2_ENG_NA = 0, // Null instruction tag - acts as ENDSEQ
    R2U2_ENG_SY = 1, // System commands - reserved for monitor control
    R2U2_ENG_CG = 2, // Immediate Configuration Directive
    R2U2_ENG_AT = 3, // Original Atomic Checker
    R2U2_ENG_TL = 4, // MLTL Temporal logic engine
    R2U2_ENG_BZ = 5, // Booleanizer
} r2u2_engine_tag_t;
```

Of these six values, only three are "real" (AT, BZ, and TL), while the other three are used internally by the monitor for signaling.

## Instruction Dispatch

The `r2u2_instruction_dispatch` function contains the primary control flow of the monitor.
using the state of the vector clock variables, the next instruction is selected from memory and executed if appropriate.
Rollover behavior (such as reaching the end of the program and resetting the program counter) is also handled here.

If an instruction is accepted, the engine tag is used to call the respective instruction dispatch function (for example `r2u2_mltl_instruction_dispatch`) and advancing ht program counter for the next instruction.

## Atomic Checker (AT)

One of two front-ends available to convert external signals into Boolean values for use by the temporal logic engine, the Atomic Checker uses a limited but powerful structure originally designed for the R2U2 hardware monitor to minimize FPGA fabric.

See the C2PO documentation to generate AT instructions, and a description of their architecture in {footcite:p}`KZJZR20`.

## Booleanizer (BZ)

The Booleanizer is a more general computation engine for front-end processing.
Its capabilities and operation are detailed in the C2PO documentation.

## Mission-time Linear Temporal Logic (TL)

Provides future-time and past-time temporal logic reasoning.

Past-time logic utilizes [box queues](./memory.md#box-queue) while future-time logic uses [shared connection queues](./memory.md#shared-connection-queues) for working memory.

The queue sizing is the primary reason the monitor might need to walk the program instructions multiple times per time-step and is the source of the progress checks.

The internal architecture of the monitors is described in {footcite:p}`KZJZR20`.

---

:::{footbibliography}
:::
