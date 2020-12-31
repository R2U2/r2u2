
#ifndef R2U2_H
#define R2U2_H

#include <stdio.h>

#define R2U2_C_VERSION_MAJOR 1
#define R2U2_C_VERSION_MINOR 0

#ifdef DEBUG
    #define DEBUG_PRINT(...) do{ fprintf( stderr, __VA_ARGS__ ); } while( false )
#else
    #define DEBUG_PRINT(...) do{ } while ( false )
#endif

#ifdef AT_DEBUG
    // Print to stdout so user can pipe output to file more easily
    #define AT_LOG(...) do{ fprintf( stdout, __VA_ARGS__ ); } while( false )
#else
    #define AT_LOG(...) do{ } while ( false )
#endif

#ifdef DEEP_DEBUG
    #define DEEP_PRINT(...) do{ fprintf( stderr, __VA_ARGS__ ); } while( false )
#else
    #define DEEP_PRINT(...) do{ } while ( false )
#endif

#endif
