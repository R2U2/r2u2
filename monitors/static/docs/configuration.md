# Configuration

While the R2U2 static monitor supports runtime configuration of specifications, two types of compile-time configuration also exists for tuning monitor behavior and performance, [](#bounds) and [](#feature-flags).

---

## Bounds

Bounds are numeric limits set as C pre-processor macros which are used primarily to set array and memory arena sizes.
Using fixed memory bounds allows for fast, consistent operation without memory allocation (e.g., if it loads, it won't OOM) at the cost of requiring manual tuning for optimal performance.

If these numbers must be adjusted, it is most consistent to do so in the `internals/bounds.h` file where they are defined to ensure the same value is set in all locations.
It is recommend to run with debug output after changing bounds to enable extra memory size checks.


### Array Extents

`R2U2_MAX_INSTRUCTIONS`
: Maximum number of instructions that will be read from a specification binary. Also used for some debug printing
: Default: 256

`R2U2_MAX_SIGNALS`
: Size of incoming signal vector, i.e., maximum number of signals. Only used by default monitor constructor
: Default: 256

`R2U2_MAX_ATOMICS`
: Size of atomic vector, i.e., maximum number of Booleans passed from the front-end (AT or BZ) to the temporal logic engine
: Default: 256

`R2U2_MAX_INST_LEN`
: Total size of instruction memory, i.e., maximum specification binary size. Only used by default monitor constructor
: Default: 8192

`R2U2_MAX_AT_INSTRUCTIONS`
: Maximum number of AT instructions, actually used to reserve filter memory for extended filters like rate and moving average. Only used by default monitor constructor
: Default: 256

`R2U2_MAX_BZ_INSTRUCTIONS`
: Size of value buffer, used as working memory by BZ front end. Only used by default monitor constructor
: Default: 256


### Memory Arena Sizing

`R2U2_MAX_AUX_STRINGS`
: Total characters (and nulls) of string arena used by auxiliary output (e.g., formula names, contract names, etc.) if enabled.
: Default: 1024

`R2U2_MAX_BOXQ_BYTES`
: Arena size in bytes used for past-time reasoning
: Default: 256 * 1024

`R2U2_MAX_SCQ_BYTES`
: Arena size in bytes used for future-time reasoning
: Default: 256 * 1024

### Numeric Parameters

`R2U2_FLOAT_EPSILON`
: Sets the error value used for float comparisons (i.e., how close is considered "equal").
: Default: 0.00001

---

## Feature Flags

Feature flags are C pre-processor macros that are used to conditionally compile features in or out of the static monitor.
Flags are used when the feature drastically alters the behavior of the monitor, such as altering the input format, or significantly impacts monitor performance, such as code size or evaluation speed.

Feature flags are declared in and controlled by the `internals/config.h` file.
This headerfile ensures all flags are declared and performs a consistency check to prevent incompatible feature or platform combinations.

Flags can be set anywhere in the translation unit before R2U2 is included, or set environment wide though compiler define flags.
See [building the monitor](./building.md) for details.

### Logging Output

`R2U2_DEBUG`
: Enables debug printing to stderr. Also enable extra memory checks at runtime

`R2U2_TRACE`
: Enables very verbose memory trace printing to stderr


### Input Handling Features

`R2U2_CSV_Header_Mapping`
: Enables reordering header imports to match signal vector mapping


### Atomic-Checker Features

`R2U2_AT_EXTRA_FILTERS`
: Enables the Rate, Angle difference, and moving average AT filters

`R2U2_AT_Signal_Sets`
: Enables set aggregation filters

`R2U2_AT_FFT_Filter`
: :::{deprecated} 3.0
: :::
: Enables the discrete Fourier transform filter, but requires the fftw3 library

`R2U2_AT_Prognostics`
: :::{deprecated} 3.0
: Enables the prognostics module


### Temporal Logic Features

`R2U2_TL_SCQ_Verdict_Aggregation`
: Compress SCQs with verdict aggregation

`R2U2_TL_Formula_Names`
: Enables named formula verdicts

`R2U2_TL_Contract_Status`
: Enables printing tri-state reports of assume-guarantee contracts

