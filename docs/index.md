# Overview

The Realizable, Reconfigurable, Unobtrusive Unit (R2U2) is a stream-based runtime verification
framework based on Mission-time Linear Temporal Logic (MLTL) designed to monitor safety-critical or
mission-critical systems with constrained computational resources.

Given a specification and input stream, R2U2 will output a stream of verdicts computing whether the
specification holds with respect to the input stream. Specifications can be written and compiled using the
Configuration Compiler for Property Organization (C2PO).

To get started, go to the [Quick Start Guide (C Version)](Overview/quick_start_guide_c) or [Quick Start Guide (Rust Version)](Overview/quick_start_guide_rust).

If you would like to cite R2U2, please use our [2023 CAV paper](https://link.springer.com/chapter/10.1007/978-3-031-37709-9_23). 


```{toctree}
:hidden:
Overview/quick_start_guide_c
Overview/quick_start_guide_rust
Overview/installation
Overview/project_structure
```

```{toctree}
:hidden:
:caption: ✏️ MLTL Monitoring
:maxdepth: 2
:titlesonly:
Preliminaries/spec_writing
Preliminaries/mltl
Preliminaries/runtime_monitoring
```

```{toctree}
:hidden:
:caption: 📚 User Guides
_collections/c2po_docs/user/toc
_collections/r2u2_c_docs/user/toc
_collections/r2u2_rust_docs/user/toc
_collections/test_readme
examples
```

```{toctree}
:hidden:
:caption: 🛠 Developer Guides
_collections/c2po_docs/dev/toc
R2U2_Implementation
_collections/r2u2_c_docs/dev/toc
_collections/r2u2_rust_docs/dev/toc
README
_collections/CONTRIBUTING.md
```

```{toctree}
:hidden:
:caption: 📖 References
References/file_formats
References/mltl_grammar
References/publications
```

<!-- 
# Indices and tables

* {ref}`genindex`
* {ref}`modindex`
* {ref}`search` -->
