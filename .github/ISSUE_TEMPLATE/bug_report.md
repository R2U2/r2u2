---
name: Bug report
about: Create a report to help us improve
title: ''
labels: ''
assignees: ''

---

**Describe the bug**
A clear and concise description of what the bug is.

**Include specification file, input trace, and debug output**
To obtain debug output, re-compile R2U2 in debug mode:
```
cd monitors/c 
make clean debug
./build/r2u2_debug path/to/spec.bin path/to/trace.csv 2> debug.log
```

**Expected behavior**
A clear and concise description of what you expected to happen.

**Environment (please complete the following information):**
- OS: [e.g. Ubuntu 24.04]
- C Compiler: [e.g. gcc, clang]
- Python version: [e.g. 3.8, 3.10]

**Additional context**
Add any other context about the problem here.
