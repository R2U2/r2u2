# Contributing to R2U2

## **Did you find a bug?**

* **Ensure the bug was not already reported** by searching on GitHub under [Issues](https://github.com/R2U2/r2u2/issues).

* If you're unable to find an open issue addressing the problem, [open a new one](https://github.com/R2U2/r2u2/issues/new). Be sure to include a **title and clear description** and as much relevant information as possible.

* Include the specification file, input trace, and debug output causing the bug in the new issue. To obtain debug output, re-compile R2U2 in debug mode:
```
cd monitors/c
make clean debug
./build/r2u2_debug path/to/spec.bin path/to/trace.csv 2> debug.log
```

## **Did you write a patch that fixes a bug?**

* Open a new GitHub pull request with the patch.

* Ensure the PR description clearly describes the problem and solution. Include the relevant issue number if applicable.

## **Do you want to add/request a feature for R2U2?**

* Open a GitHub issue with the `enhancement` label and a complete description of the feature to start a discussion.

* If the feature is deemed acceptable:

    * Open a new branch

    * Implement the feature

    * Write new tests for the feature

    * Open a pull request referencing the discussion GitHub issue number (the one with the `enhancement` label).

## Coding Conventions

* For Python, we use [ruff](https://github.com/astral-sh/ruff) with the configuration found in [`compiler/pyproject.toml`](compiler/pyproject.toml).

* For C, we use [clang-format](https://clang.llvm.org/docs/ClangFormat.html) with the configuration found in [`monitors/c/.clang-format`](monitors/c/.clang-format).