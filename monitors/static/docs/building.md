# Building

The R2U2 static monitor as a static or shared library for use by user-developed programs, and includes an example CLI that can be used to run R2U2 specifications on the command line.

## Dependencies

The R2U2 monitor strives to minimize dependencies to ensure it can be targeted-at/ported-to as wide a variety of devices possible.
A standard build of the included R2U2 monitor CLI as provided requires:

- C99 std compiler (gcc or clang)
- Posix environment (Linux, MacOS, Etc.)
- Make

:::{note}
The requirement for make can be worked around by manually configuring your own build system (see [below](#building-without-the-makefile)) and the Posix file assumptions are primarily required the CLI in `main.c` and aren't needed when used as a library, leaving only C99 compatibility as a hard requirement for deeply embedded contexts.
:::

## The Makefile

The R2U2 static monitor includes a Makefile which automates the build process and caches results in the `build` directory.

Run "make help" for common build targets with sort descriptions.

Run "make list" for an uncommented list of all targets.

### Common Build Targets

`bin`
: Builds `build/r2u2`, a CLI executable of R2U2 in release mode

`debug`
: Builds `build/r2u2_debug`, a CLI executable of R2U2 with compile time warnings, runtime sanitizers, extra memory checks, and debug logging enabled

`shared`
: Builds `build/libr2u2.so`, a shared object library of R2U2 in release mode

`static`
: Builds `build/libr2u2.a`, a static archive of R2U2 in release mode

## Building Without the Makefile

If the provided Makefile cannot be integrated in your build environment, make sure to force your compiler into c99 standard compliance and define the POSIX flag `_POSIX_C_SOURCE=200112L` along with any [feature flags](./configuration.md#feature-flags) needed by your application.
