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
R2U2_MAX_SPECS = { value = "1024", force = true }
```
in `.cargo/config.toml`.


### Array Extents

`R2U2_MAX_SPECS`
: Maximum number of instructions that will be read from a specification binary. Also used for some debug printing
: Default: 256

`R2U2_MAX_SIGNALS`
: Size of incoming signal vector, i.e., maximum number of signals. Only used by default monitor constructor
: Default: 256

`R2U2_MAX_ATOMICS`
: Size of atomic vector, i.e., maximum number of Booleans passed from the front-end (AT or BZ) to the temporal logic engine
: Default: 256

`R2U2_MAX_BZ_INSTRUCTIONS`
: Size of value buffer, used as working memory by BZ front end. Only used by default monitor constructor
: Default: 256

`R2U2_MAX_TL_INSTRUCTIONS`
: Size of value buffer, used as working memory by TL front end. Only used by default monitor constructor
: Default: 256


### Memory Sizing

`R2U2_TOTAL_QUEUE_MEM`
: Number of SCQ slots for both future-time and past-time reasoning
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

