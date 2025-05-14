# Architecture

The R2U2 static monitor is designed to be modular, allowing performance to be finely tuned.
While default setups exist, unused features can be left out entirely to minimize memory and performance overhead.
This loose coupling also translates to strong separation of concerns and allows new modules to be added without fear of interrupting other components.

All components are divided into four categories:


[Execution Engines](./engines.md)
: Triggered by instructions, these manipulate monitor state to evaluate the specification


[Instructions](./instructions.md)
: Define instructions and how to parse them from inputted C2PO binary

[Internals](./internals.md)
: Common utilities and support functionality like error handling and debug logging

[Memory Controllers](./memory.md)
: Define data types and associated functions

The `r2u2_core` crate is written in `no_std` and includes the core of R2U2 with specified API calls. Both `r2u2_cli` and 
`r2u2_cortex_m_example` demonstrate examples of how to utilize the `r2u2_core` crate. `r2u2_cli` is directed to allow users
to utilize R2U2 through a commandline interface, and `r2u2_cortex_m_example` demonstrates how to embed R2U2 on a microcontroller.
