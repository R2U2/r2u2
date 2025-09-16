# Debug

The R2U2 Static Monitor uses two levels of debug flags with corresponding print macros.

The feature flags are set according to the procedure in the [User's Guide](./configuration.md).

## `R2U2_DEBUG`

This flag enable debug printing to the file pointer `r2u2_debug_fptr` which must be declared linked (usually by the provided `lib.c` or `cli/main.c`) as well as enabling various additional checks.

In general, the philosophy is that belt-and-suspenders checks and verification of assumptions should live behind the debug flag while a pure release build can assume the configuration has been thoroughly vetted and should target raw performance.

This level is expected to be user-facing and should communicate monitor behavior in response to inputs including signals and specifications.

## `R2U2_TRACE`

Reserved for deeper, more verbose output usefully only to R2U2 monitor developers (i.e., intrinsic to the internal design) and not just in response to user input.
If this is on, something very weird is happening; you probably need to break out a hex calculator, and should expect to write a new test at the end of the bug hunt.

## Debug Printing

Debug printing is done via the `R2U2_DEBUG_PRINT` and `R2U2_TRACE_PRINT` macros which are defined using a do-while structure:
```C
#if R2U2_DEBUG
    extern FILE* r2u2_debug_fptr;
    #define R2U2_DEBUG_PRINT(...) do{ if (r2u2_debug_fptr != NULL) {fprintf( r2u2_debug_fptr, __VA_ARGS__ );} } while( false )
#else
    #define R2U2_DEBUG_PRINT(...)
#endif

#if R2U2_TRACE
    #define R2U2_TRACE_PRINT(...) do{ fprintf( stderr, __VA_ARGS__ ); } while( false )
#else
    #define R2U2_TRACE_PRINT(...)
#endif
```

This allows the macros to be used like real functions, with a trailing semicolon, in all locations a `printf` would be expected to work.
The empty do-while-false structure emitted in non-debug builds will be compiled out, leaving no overhead of the debug prints in release build.
For a discussion of why this approach is needed in C99, see [here](https://stackoverflow.com/questions/1644868/define-macro-for-debug-printing-in-c).
