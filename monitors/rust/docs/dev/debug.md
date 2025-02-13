# Debug

The `r2u2_core` crate has two optional features to enable debugging:

- `debug_print_std`: Debug printing to terminal (i.e., println!)

- `debug_print_semihosting`: Debug printing utilizing GDB debugger of microcontroller (i.e., hprintln!)

Enable by specifying the feature when declaring dependency in `Cargo.toml`:
:For example:  
```
r2u2_core={path="../r2u2_core", features = ["debug_print_std"]}
```