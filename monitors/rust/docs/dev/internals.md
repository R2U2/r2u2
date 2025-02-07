# Internals

The internals subdirectory provides several common/utility facilities to both memory controllers and execution engines:

`bounds.rs`
: Define and check compile-time configuration of the monitor. See the [User's Guide](../user/configuration.md) for details on setting parameters.

`debug.rs`
: Provides debug print definitions, including utilizing `println!` and `hprintln!`. See [Debug](./debug.md) for more details.

`process_binary.rs`
: Takes the binary specification file, parses it, applies appropriate configuration commands, and stores instructions in applicable instruction tables.

`types.rs`
: Definitions of parameterize types common to all components of the monitor, allowing for type punning.
