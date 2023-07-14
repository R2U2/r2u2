#ifndef R2U2_TYPES_H
#define R2U2_TYPES_H

#include <stddef.h>   // For size_t (used elsewhere but assumed in types.h)
#include <stdbool.h>  // For booleans
#include <stdint.h>

#include "internals/bounds.h"

// Punning
#ifndef r2u2_bool
    #define r2u2_bool bool
#endif

#ifndef r2u2_int
    // Meant to define a signal / AT or BZ int size
    // TODO(bckempa): in use by Box Queues, to be changed....
    #define r2u2_int int32_t
#endif

#ifndef r2u2_float
    #define r2u2_float double
#endif

#ifndef r2u2_time
    // R2U2 timestamp type, assumed to be an unsigned integer
    #define r2u2_time unsigned int
#endif

#ifndef r2u2_infinity
    // If not defined (i.e. limited), assumed to be max of r2u2_time
    // per §6.2.5/9 casting negative 1 to unsigned int gives max value
    #define r2u2_infinity ((r2u2_time)-1)
#endif

// TODO(bckempa): Need a type gurenteed for indexing
//                (see binary_load.c)

// Consistency Checks
// https://stackoverflow.com/questions/174356/ways-to-assert-expressions-at-build-time-in-c

// Common Derived Types

typedef struct {
    // Truth & Time
    r2u2_bool truth;
    r2u2_time time;
} r2u2_verdict;

typedef union r2u2_value {
    r2u2_bool b;
    r2u2_int i;
    r2u2_float f;
} r2u2_value_t;


#endif /* R2U2_TYPES_H */
