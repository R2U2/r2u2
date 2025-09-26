#ifndef R2U2_TYPES_H
#define R2U2_TYPES_H

#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include "bounds.h"

// Use with care! Much better to leave off than be wrong; really only for one-off
// branches, like first time checks.
#define r2u2_likely(x)       __builtin_expect(!!(x), 1)
#define r2u2_unlikely(x)     __builtin_expect(!!(x), 0)

// Punning
#ifndef r2u2_bool
    #define r2u2_bool bool
#endif

#ifndef r2u2_int
    #define r2u2_int int32_t
#endif

#ifndef r2u2_float
    #define r2u2_float double
#endif

#ifndef r2u2_time
    // R2U2 timestamp type, assumed to be an unsigned 32-bit integer
    #define r2u2_time uint32_t
#endif

#ifndef r2u2_addr
    #define r2u2_addr uint32_t
#endif

#ifndef r2u2_infinity
    // If not defined (i.e. limited), assumed to be max of r2u2_time
    // per §6.2.5/9 casting negative 1 to unsigned int gives max value
    #define r2u2_infinity ((r2u2_time)-1)
#endif

// Common Derived Types

/* Verdict-timestamp tuple in single r2u2_time value.
 * Combines truth (as the MSB) and the timestamp (as the other 31 bits) into a single value.
 * Typdefed separately to ensure differentiation from pure timestamps.
 * This signficantly improves queue memory effiency since booleans took full
 * bytes and then required additioanl padding wasting about 31 bits per queue
 * slot depending on the platform and timestep width.
 */
typedef r2u2_time r2u2_verdict;
static const r2u2_verdict R2U2_TNT_TIME = (((r2u2_verdict)-1) >> 1);
static const r2u2_verdict R2U2_TNT_TRUE = ~R2U2_TNT_TIME;

/// @brief      Inline function that returns truth bit of verdict-timestamp tuple
/// @param[in]  result  Verdict-timestamp tuple of type r2u2_verdict
/// @return     r2u2_bool Boolean representing truth bit (MSB)
static inline __attribute__((always_inline)) r2u2_bool get_verdict_truth(r2u2_verdict result){
    return result & R2U2_TNT_TRUE;
}

/// @brief      Inline function that returns timestamp of verdict-timestamp tuple
/// @param[in]  result  Verdict-timestamp tuple of type r2u2_verdict
/// @return     r2u2_time Integer representing the timestamp (31 LSBs)
static inline __attribute__((always_inline)) r2u2_time get_verdict_time(r2u2_verdict result){
    return result & R2U2_TNT_TIME;
}

/// @brief      Inline function that sets the truth bit to true and returns tuple
/// @param[in]  time  Verdict-timestamp tuple (or just a timestamp) of type r2u2_verdict
/// @return     r2u2_verdict Verdict-timestamp tuple with the truth bit set to true
static inline __attribute__((always_inline)) r2u2_verdict set_verdict_true(r2u2_verdict time){
    return time | R2U2_TNT_TRUE;
}

/// @brief      Inline function that sets the truth bit to false and returns tuple
/// @param[in]  time  Verdict-timestamp tuple (or just a timestamp) of type r2u2_verdict
/// @return     r2u2_verdict Verdict-timestamp tuple with the truth bit set to false
static inline __attribute__((always_inline)) r2u2_verdict set_verdict_false(r2u2_verdict time){
    return time & R2U2_TNT_TIME;
}

typedef union {
    // Notice that we store booleans as integers so we do not require 
    // boolean specific instructions (e.g., BLOAD or BADD)
    r2u2_int i;
    r2u2_float f;
} r2u2_value_t;


#endif /* R2U2_TYPES_H */
