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


The `r2u2_step` function contains the primary control flow of the monitor. All booleanizer instructions are executed first and 
only once. Then the temporal logic instructions are sequentially iterated over until no more progress can be made based on the
currently observed data.

Booleanizer instructions are handled by `bz_update` and temporal_logic instructions are handled by `mltl_update`.

## Booleanizer (BZ)

The Booleanizer is a more general computation engine for front-end processing.
Its capabilities and operation are detailed in the C2PO documentation.

## Mission-time Linear Temporal Logic (TL)

Provides future-time and past-time temporal logic reasoning.

Past-time and future-time logic uses [shared connection queues](./memory.md#shared-connection-queue) for working memory.

The queue sizing is the primary reason the monitor might need to walk the program instructions multiple times per time-step and is the source of the progress checks.

The internal architecture of the monitors is described in {footcite:p}`AJR2025` and {footcite:p}`KZJZR20`.

## Auxiliary Info
An optional engine to print assume-guarantee contract status and formula names when reporting verdicts. Option is
enabled with the `R2U2_AUX_STRING_SPECS` feature flag.

Contract status allows the use of the `=>` operator in C2PO to enable a tri-state output of assume-guarantee contracts.
During formula compilation, each AGC is broken into three MLTL formulas, one for each state - inactive, verified, or violated.
This forms a "one-hot" encoding where the truth value of each formula corresponds to one of the three states.

The `r2u2_aux_info_arena_t` provides the memory backing for the additional auxilary instruction storage (defined in `instructions/aux_info.h`).
Then, `r2u2_aux_formula_report` is used to report verdict status based on formula string name, and `r2u2_aux_contract_report` is used to check if newly produced verdicts also correspond to a contract status.

---

:::{footbibliography}
:::
