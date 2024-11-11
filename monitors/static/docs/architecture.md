# Architecture

The R2U2 static monitor is designed to be modular, allowing performance to be finely tuned.
While default setups exist, unused features can be left out entirely to minimize memory and performance overhead.
This loose coupling also translates to strong separation of concerns and allows new modules to be added without fear of interrupting other components.

All components are divided into three categories:

[Internals](./internals.md)
: Common utilities and support functionality like error handling and debug logging

[Memory Controllers](./memory.md)
: Define data types and associated functions

[Execution Engines](./engines.md)
: Triggered by instructions, these manipulate monitor state to evaluate the specification

In general, to maintain separation of concerns, memory domains may be read by any engine, but are only modified by a single engine.

Additionally, `main.c` provides a reference implementation showcasing how to setup and run an R2U2 monitor.
