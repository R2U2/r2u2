# Installation
> More details on environment setup and platform compatibility

While the requirements of the individual monitors are quite small, setting up an environment for developing with all R2U2 sub-projects is more involved.
This is usually unnecessary for most users.

:::{hint}
Most dependencies, especially development tooling, are installed via Pythons packaging infrastructure and therefore a Python virtual environment is **strongly** recommended.
:::

## C2PO

Usage:
- Python >= 3.7
- `pip install typing-extensions`

Development:
- `pip install pytest`
- `pip install numpy`


## R2U2

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
