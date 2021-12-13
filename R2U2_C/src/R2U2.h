
#ifndef R2U2_H
#define R2U2_H

/* Compiler version check */
#if (__STDC_VERSION__ < 199409L)
    #error R2U2 requires C99 or higher
#endif

/* Enable POSIX.1 complaint fmemopen in stdio.h when building with -std=c99. */
#define _POSIX_C_SOURCE 200112L

#include <stdio.h>
#include "R2U2Config.h"

#define R2U2_C_VERSION_MAJOR 2
#define R2U2_C_VERSION_MINOR 0
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

#ifndef R2U2_AT_Extra_Filters
    /* Enables the Rate, Angle difference, and moving average AT filters */
    #define R2U2_AT_Extra_Filters INHIBIT
#endif

#ifndef R2U2_AT_FFT_Filter
    /* Enables the discrete Fourier transform filter,
     * but requires the fftw3 library */
    #define R2U2_AT_FFT_Filter INHIBIT
#endif

#ifndef R2U2_AT_Prognostics
    /* Enables the prognostics module */
    #define R2U2_Prognostics INHIBIT
#endif

#ifndef R2U2_AT_Signal_Sets
    /* Enables set aggregation filters */
    #define R2U2_AT_Signal_Sets INHIBIT
#endif

#ifndef R2U2_TL_Formula_Names
    /* Enables named formula verdicts */
    #define R2U2_TL_Formula_Names INHIBIT
#endif

#ifndef R2U2_TL_Contract_Status
    /* Enables printing tri-state reports of assume-guarantee contracts */
    #define R2U2_TL_Contract_Status INHIBIT
#endif

#ifndef R2U2_CSV_Header_Mapping
    /* Enables reordering header imports to match signal vector mapping */
    #define R2U2_CSV_Header_Mapping INHIBIT
#endif

#ifndef R2U2_DEBUG
    /* Enables debug printing to stderr */
    #define R2U2_DEBUG INHIBIT
#endif

#ifndef R2U2_TRACE
    /* Enables memory trace printing to stderr */
    #define R2U2_TRACE INHIBIT
#endif

// TODO: Require a flag for unsupported platform builds?
/* Platform compatibility enforcement, this will intentionally cause a
 * pre-processor warning a feature status is changed due to platform
 */
#if defined(__linux__)
    // No known feature incompatibilities
#elif defined(__APPLE__)
    // No known feature incompatibilities
#elif defined(__VXWORKS__)
    #define R2U2_AT_Extra_Filters INHIBIT
    #define R2U2_AT_FFT_Filter INHIBIT
    #define R2U2_Prognostics INHIBIT
#elif defined(_WIN32)
    // No known feature incompatibilities
    // #warning Windows is an unsupported platform
#else
    // #warning Unknown, unsupported platform
#endif

/* Debug Conditionals */
// TODO: Make R2U2_DEBUG with levels and add location info
// e.g.: R2U2_DEBUG_PRINT(fmt, args...) fprintf(stderr, "DEBUG: %s:%d:%s(): " fmt, __FILE__, __LINE__, __func__, ##args)
// Good reference: https://stackoverflow.com/questions/1644868/define-macro-for-debug-printing-in-c
#if R2U2_DEBUG
    extern FILE* r2u2_debug_fptr;
    #define R2U2_DEBUG_PRINT(...) do{ if (r2u2_debug_fptr != NULL) {fprintf( r2u2_debug_fptr, __VA_ARGS__ );} } while( false )
#else
    #define R2U2_DEBUG_PRINT(...) do{ } while ( false )
#endif

#if R2U2_TRACE
    #define R2U2_TRACE_PRINT(...) do{ fprintf( stderr, __VA_ARGS__ ); } while( false )
#else
    #define R2U2_TRACE_PRINT(...) do{ } while ( false )
#endif

#endif
