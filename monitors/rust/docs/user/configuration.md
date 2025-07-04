# Configuration

While the R2U2 static monitor supports runtime configuration of specifications, two types of compile-time configuration also exists for tuning monitor behavior and performance, [](#bounds) and [](#features).

More information also available at [https://docs.rs/r2u2_core/latest/r2u2_core/](https://docs.rs/r2u2_core/latest/r2u2_core/).

---

## Bounds

Bounds are numeric limits set as Rust pre-processor macros which are used primarily to set array and memory sizes.
Using fixed memory bounds allows for memory-safe Rust performance.

If these numbers must be adjusted, it is most consistent to do so in the `bounds.rs` file or overwrite values in parent application, e.g., include something like
```
[env]
R2U2_MAX_OUTPUT_VERDICTS = { value = "1024", force = true }
```
in `.cargo/config.toml`.


### Array Extents

`R2U2_MAX_OUTPUT_VERDICTS`
: Maximum number of output verdicts that can be returned at a single timestamp
: Default: 256

`R2U2_MAX_OUTPUT_CONTRACTS`
: Maximum number of output contract statuses that can be returned at a single timestamp
: Default: 256

`R2U2_MAX_SPECS`
: Maximum number of specifications being monitored
: Default: 256

`R2U2_MAX_SIGNALS`
: Maximum number of input signals
: Default: 256

`R2U2_MAX_ATOMICS`
: Maximum number of Booleans passed from the front-end (booleanizer or directly loaded atomics) to the temporal logic engine
: Default: 256

`R2U2_MAX_BZ_INSTRUCTIONS`
: Maximum number of booleanizer instructions
: Default: 256

`R2U2_MAX_TL_INSTRUCTIONS`
: Maximum number of temporal logic instructions
: Default: 256


### Memory Sizing

`R2U2_TOTAL_QUEUE_SLOTS`
: Total number of SCQ slots for both future-time and past-time reasoning
: Default: 2048

### Numeric Parameters

`R2U2_FLOAT_EPSILON`
: Sets the error value used for float comparisons (i.e., how close is considered "equal").
: Default: 0.00001

:::{note} `R2U2_FLOAT_EPSILON` can only be changed in `bounds.rs`.
:::

---

## Features

`r2u2_core` has the following optional features:
- aux_string_specs: Enable Assume-Guarantee Contract status output and string auxiliary specification naming.
- debug_print_std: Debug printing to terminal (i.e., println!)
- debug_print_semihosting: Debug printing utilizing GDB debugger of microcontroller (i.e., hprintln!)

