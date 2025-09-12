#ifndef R2U2_BOUNDS_H
#define R2U2_BOUNDS_H

// Size of string arena, in bytes, for auxillary output
// Only reserved if R2U2_AUX_STRING_SPECS is enabled
#define R2U2_MAX_AUX_BYTES 1024

// Represents maximum number of formulas being monitored
// Only reserved if R2U2_AUX_STRING_SPECS is enabled
#define R2U2_MAX_FORMULAS 128

// Represents maximum number of assume-guarantee contracts being monitored
// Only reserved if R2U2_AUX_STRING_SPECS is enabled
#define R2U2_MAX_CONTRACTS 64

// Represents maximum number of input signals
#define R2U2_MAX_SIGNALS 256

// Represents maximum number of Booleans passed from the front-end
// (booleanizer or directly loaded atomics) to the temporal logic engine
#define R2U2_MAX_ATOMICS 256

// Represents maximum number of booleanizer instructions
#define R2U2_MAX_BZ_INSTRUCTIONS 256

// Represents maximum number of temporal logic instructions
#define R2U2_MAX_TL_INSTRUCTIONS 256

// Represents total number of SCQ slots for both future-time and past-time reasoning
#define R2U2_TOTAL_QUEUE_SLOTS 1024

#define R2U2_FLOAT_EPSILON 0.00001

#endif /* R2U2_BOUNDS_H */
