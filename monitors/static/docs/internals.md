# Internals

The internals subdirectory provides several common/utility facilities to both memory controllers and execution engines:

`bounds.h` and `config.h`
: Define and check compile-time configuration of the monitor. See the [User's Guide](./configuration.md) for details on setting parameters.
: :::{caution} To allow undefined preprocessors definitions to be detected as an error state, all flags must be defined in `config.h` and set to either `EXHIBIT` or `INHIBIT` (i.e., `1` or `0`) and only checked for value - never existence!

`debug.h`
: Provides debug preprocessor definitions, including printing macros and an `UNUSED` marker. See [debug](./debug.md) for more details.

`errors.h` and `errors.c`
: Defines the `r2u2_status` enum used to signal error conditions throughout the monitor, as well as string conversion facilities for errors when in debug mode.

`types.h`
: Definitions of parameterize types common to all components of the monitor, allowing for type punning.
