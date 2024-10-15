#ifndef R2U2_TYPES_H
#define R2U2_TYPES_H

#include <stddef.h>   // For size_t (used elsewhere but assumed in types.h)
#include <stdbool.h>  // For booleans
#include <stdint.h>
#include <string.h> // memcpy
#include <limits.h> // CHAR_BIT

#include "internals/bounds.h"

// Use with care! Much better leave off than be wrong, really only for one-off
// branches, like first time checks.
#define r2u2_likely(x)       __builtin_expect(!!(x), 1)
#define r2u2_unlikely(x)     __builtin_expect(!!(x), 0)

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
    // R2U2 timestamp type, assumed to be an unsigned 32-bit integer
    #define r2u2_time uint32_t
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

/* Truth-n'-Time (TNT)
 * Combines truth (as the MSB) and the timestamp into a single value.
 * Typdefed seperatly to ensure differentiation from pure timestamps.
 * This signficantly improves queue memory effiency since booleans took full
 * bytes and then required additioanl padding wasting about 31 bits per queue
 * slot depending on the platform and timestep width.
 */
typedef r2u2_time r2u2_tnt_t;
static const size_t R2U2_TNT_BITS = sizeof(r2u2_tnt_t) * CHAR_BIT;
static const r2u2_tnt_t R2U2_TNT_TIME = (((r2u2_tnt_t)-1) >> 1);
static const r2u2_tnt_t R2U2_TNT_TRUE = ~R2U2_TNT_TIME;
static const r2u2_tnt_t R2U2_TNT_FALSE = 0;

typedef struct {
    // Time & Truth
    r2u2_time time;
    r2u2_bool truth;
} r2u2_verdict;

typedef union r2u2_value {
    r2u2_bool b;
    r2u2_int i;
    r2u2_float f;
} r2u2_value_t;


#endif /* R2U2_TYPES_H */
