#ifndef R2U2_DEBUG_H
#define R2U2_DEBUG_H

#include <stdio.h>
#include <stdbool.h>
#include "../internals/config.h"

/* Portable form of marking unused  */
// From: https://stackoverflow.com/a/3599170 [CC BY-SA 3.0]
#define UNUSED(x) (void)(x)

/* Debug Conditionals */
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

#endif /* R2U2_DEBUG_H */
