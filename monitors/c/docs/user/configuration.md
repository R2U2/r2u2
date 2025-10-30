# Configuration

While the R2U2 static monitor supports runtime configuration of specifications, two types of compile-time configuration also exists for tuning monitor behavior and performance, [](#bounds) and [](#feature-flags).

---

## Bounds

Bounds are numeric limits set as C pre-processor macros which are used primarily to set array and memory arena sizes.
Using fixed memory bounds allows for fast, consistent operation without memory allocation (e.g., if it loads, it won't OOM) at the cost of requiring manual tuning for optimal performance.

If these numbers must be adjusted, it is most consistent to do so in the `internals/bounds.h` file where they are defined to ensure the same value is set in all locations.
It is recommend to run with debug output after changing bounds to enable extra memory size checks.


### Array Extents

`R2U2_AUX_MAX_FORMULAS`
: Number of formula auxilary information metadata blocks; only utilized when `R2U2_AUX_SPEC_STRINGS` feature is enabled. 
: Default: 128

`R2U2_AUX_MAX_CONTRACTS`
: Number of assume-guarantee contract (AGC) auxilary information metadata blocks; only utilized when `R2U2_AUX_SPEC_STRINGS` feature is enabled. 
: Default: 64

`R2U2_MAX_SIGNALS`
: Size of incoming signal vector, i.e., maximum number of signals. 
: Default: 256

`R2U2_MAX_ATOMICS`
: Size of atomic vector, i.e., maximum number of Booleans passed from the front-end (BZ) to the temporal logic engine
: Default: 256

`R2U2_MAX_TL_INSTRUCTIONS`
: Size of temporal logic instruction table and number of SCQ metadata blocks; used as working memory by TL front end. 
: Default: 256

`R2U2_MAX_BZ_INSTRUCTIONS`
: Size of booleanizer instruction table and value buffer; used as working memory by BZ front end. 
: Default: 256


### Memory Arena Sizing

`R2U2_MAX_AUX_BYTES`
: Total characters (and nulls) of string arena used by auxiliary output (e.g., formula names, contract names, etc.) ; only utilized when `R2U2_AUX_SPEC_STRINGS` feature is enabled. 
: Default: 1024

`R2U2_MAX_SCQ_SLOTS`
: Total number of SCQ slots for both future-time and past-time reasoning
: Default: 1024

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


### Temporal Logic Features

`R2U2_AUX_STRING_SPECS`
: Enables printing of named formula verdicts and tri-state reports of assume-guarantee contracts

