# Building

The R2U2 static monitor is available as a Rust library for use by user-developed programs, and there is also an example CLI that can be used to run C2PO specifications on the command line.

## Dependencies

The R2U2 monitor strives to minimize dependencies to ensure it can be targeted-at/ported-to as wide a variety of devices possible.
A standard build of the included R2U2 monitor CLI as provided requires:

- Posix environment (Linux, MacOS, Etc.)
- Python3 (version 3.9 or greater)
- [Rust](https://www.rust-lang.org/tools/install) 1.82.0 or greater

:::{note}
Building just `r2u2_core` as discussed when [embedding](./embedding.md) only requires [Rust](https://www.rust-lang.org/tools/install) 1.82.0 or greater.
:::

## Build the R2U2 CLI interface

There are two options:
1. Build locally with the following:

```
cd r2u2_cli
cargo build --release
```

2. Install public version from [crates.io](https://crates.io/crates/r2u2_cli/)

```
cargo install r2u2_cli
```
