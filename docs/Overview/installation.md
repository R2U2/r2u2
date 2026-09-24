# Installation
> More details on environment setup and platform compatibility

While the requirements of the individual monitors are quite small, setting up an environment for developing with all R2U2 sub-projects is more involved.
This is usually unnecessary for most users.

:::{hint}
Most dependencies, especially development tooling, are installed via Pythons packaging infrastructure and therefore a Python virtual environment is **strongly** recommended.
:::

## C2PO

Usage:
- Python >= 9
- `pip install typing-extensions`
- (Optional) To enable satisfiability checking, install [Z3](https://github.com/Z3Prover/z3)

## R2U2 (C Version)

Usage:
- A C99 compatible compiler (`gcc` or `clang`)
- Make
    
Development:
- llvm
- gcov
- gcovr
- compiledb
- compdb
- infer
- cpplint
- CodeChecker

## R2U2 (Rust Version)

Usage:
- Python >= 9
- [Rust](https://www.rust-lang.org/tools/install) 1.82.0 or greater 
