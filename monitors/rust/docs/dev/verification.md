# Verification

`r2u2_core` is verified with [Verus](https://github.com/verus-lang/verus). To run verification, one must do the following:
1. Install [Verus](https://github.com/verus-lang/verus/blob/main/BUILD.md)
2. Locate to the `r2u2_core` directory
2. Run `cargo build -v` and copy all dependencies after `-L` on the last output
3. Run Verus with the following:
```
<path_to_verus>/target-verus/release/verus --crate-type=lib src/lib.rs --compile -L <dependency_paths_copied>
```