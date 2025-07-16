#ifndef R2U2_BOUNDS_H
#define R2U2_BOUNDS_H

#define R2U2_MAX_INSTRUCTIONS 256
#define R2U2_MAX_SIGNALS 256
#define R2U2_MAX_ATOMICS 256
#define R2U2_MAX_INST_LEN 8192

#define R2U2_MAX_BZ_INSTRUCTIONS 256

// Size of string arena, in bytes, for auxillary output
// Only reserved if used
#define R2U2_MAX_SIGNAL_LABEL 140 //Max length of a specification label
#define R2U2_MAX_AUX_STRINGS R2U2_MAX_INSTRUCTIONS * R2U2_MAX_SIGNAL_LABEL

// Future Time Memory
//  SCQ_BYTES: arena size in bytes
#define R2U2_SCQ_BYTES (256 * 1024)

#define R2U2_FLOAT_EPSILON 0.00001

#endif /* R2U2_BOUNDS_H */
