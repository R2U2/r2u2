
#ifndef R2U2_CONFIG_H
#define R2U2_CONFIG_H

/* Compiler version check */
#if (__STDC_VERSION__ < 199409L)
    #error R2U2 requires C99 or higher
#endif

/* Enable POSIX.1 complaint fmemopen in stdio.h when building with -std=c99. */
#define _POSIX_C_SOURCE 200112L

#define R2U2_C_VERSION_MAJOR 4
#define R2U2_C_VERSION_MINOR 1
#define R2U2_C_VERSION_PATCH 0

/* Target and feature flags */
/* Conditional compilation in R2U2:
 * All conditional compilation should be done using the "R2U2_with" macro to
 * test the value (not existence!) on an R2U2 feature flag.
 *
 * All feature flags should be defined below.
 *
 * Platform checks should only be done once, here, and used to override
 * flag settings as needed.
 *
 * Feature flag definitions are gated by definition checks to give precedence
 * to command line definitions (e.g. -DDEBUG or -DAT_FFT=0) with a default
 * state (exhibit or inhibit) and description.
 */
#define EXHIBIT 1
#define INHIBIT 0
#define R2U2_WITH(X) R2U2_##X

#ifndef R2U2_AUX_STRING_SPECS
    /* Enables named formula verdicts and  tri-state reports of assume-guarantee contracts*/
    #define R2U2_AUX_STRING_SPECS INHIBIT
#endif

#ifndef R2U2_DEBUG
    /* Enables debug printing to stderr */
    #define R2U2_DEBUG INHIBIT
#endif

#ifndef R2U2_TRACE
    /* Enables memory trace printing to stderr */
    #define R2U2_TRACE INHIBIT
#endif

#if defined(__GNUC__)
    #define ALWAYS_INLINE __attribute__((always_inline))
#elif defined( __llvm__)
    #define ALWAYS_INLINE __attribute__((always_inline))
#endif

/* Platform compatibility enforcement, this will intentionally cause a
 * pre-processor warning a feature status is changed due to platform
 */
#if defined(__linux__)
    // No known feature incompatibilities
#elif defined(__APPLE__)
    // No known feature incompatibilities
#elif defined(__VXWORKS__)
    // No known feature incompatibilities
#elif defined(_WIN32)
    // No known feature incompatibilities
    #warning Windows is an unsupported platform
#else
    #warning Unknown, unsupported platform
#endif

#endif /* R2U2_CONFIG_H */
