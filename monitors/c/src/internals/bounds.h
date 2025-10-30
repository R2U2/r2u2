#ifndef R2U2_BOUNDS_H
#define R2U2_BOUNDS_H

// Size of string arena, in bytes, for auxillary output
// Only reserved if R2U2_AUX_STRING_SPECS is enabled
#define R2U2_MAX_AUX_BYTES 1024

// Number of formula auxilary information metadata blocks 
// Represents maximum number of formulas being monitored
// Only reserved if R2U2_AUX_STRING_SPECS is enabled
#define R2U2_MAX_FORMULAS 128

// Number of assume-guarantee contract (AGC) auxilary information metadata blocks
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

// Represents maximum number of temporal operators (i.e., F,G,U,R,O,H,T,S)
#define R2U2_MAX_TEMPORAL_OPERATORS 128

// Represents total number of SCQ slots for both future-time and past-time reasoning
#define R2U2_MAX_QUEUE_SLOTS 2048

// Represents amount of inaccuracy allowed when comparing floats
#define R2U2_FLOAT_EPSILON 0.00001

#endif /* R2U2_BOUNDS_H */
