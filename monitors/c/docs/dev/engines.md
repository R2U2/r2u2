# Execution Engines

Each engine is identified by a constant value:

```C
const uint8_t R2U2_ENG_CG: u8 = 2; // Immediate Configuration Directive
// Original Atomic Checker was 3, but has been removed since v4.0
const uint8_t R2U2_ENG_TL: u8 = 4; // MLTL Temporal logic engine
const uint8_t R2U2_ENG_BZ: u8 = 5; // Booleanizer
```

Of these three values, only two are "real" (BZ and TL), while CG is used internally by the monitor for signaling.

## Instruction Dispatch

The `r2u2_instruction_dispatch` function contains the primary control flow of the monitor.
using the state of the vector clock variables, the next instruction is selected from memory and executed if appropriate.
Rollover behavior (such as reaching the end of the program and resetting the program counter) is also handled here.

If an instruction is accepted, the engine tag is used to call the respective instruction dispatch function (for example `r2u2_mltl_instruction_dispatch`) and advancing ht program counter for the next instruction.

## Booleanizer (BZ)

The Booleanizer is a more general computation engine for front-end processing.
Its capabilities and operation are detailed in the C2PO documentation.

## Mission-time Linear Temporal Logic (TL)

Provides future-time and past-time temporal logic reasoning.

Past-time and future-time logic uses [shared connection queues](./memory.md#shared-connection-queue) for working memory.

The queue sizing is the primary reason the monitor might need to walk the program instructions multiple times per time-step and is the source of the progress checks.

The internal architecture of the monitors is described in {footcite:p}`AJR2025` and {footcite:p}`KZJZR20`.

---

:::{footbibliography}
:::
