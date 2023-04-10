#ifndef R2U2_DEBUG_H
#define R2U2_DEBUG_H

#include <stdio.h>
#include <stdbool.h>

/* Portable form of makring unused  */
// From: https://stackoverflow.com/a/3599170 [CC BY-SA 3.0]
#define UNUSED(x) (void)(x)

/* Debug Conditionals */
// TODO(bckempa): Make R2U2_DEBUG with levels and add location info
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

#endif /* R2U2_DEBUG_H */
