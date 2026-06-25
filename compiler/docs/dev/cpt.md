# C2PO Parse Tree

The C2PO Parse Tree (CPT), defined in `c2po/cpt.py`, is the core IR used across parsing, type
checking, transforms, optimization, SMT encoding, and assembly.

## Core Structures

- `Program`: section-level container (`INPUT`, `STRUCT`, `ENUM`, `DEFINE`, `FTSPEC`, `PTSPEC`) and
  FT/PT spec sets.
- `Context`: mutable compiler state (definitions, symbols, signal mapping, atomics, constraints for
  `.equiv`, generated assembly/binary, stats, and tool paths).
- `Expression` graph: formulas/operators/signals/constants used by all passes and emitters.

## Traversals and Rewrites

Most command implementations walk expressions with traversal helpers:

- `postorder(...)` for bottom-up analyses/transforms
- `preorder(...)` for top-down transforms/inspection

These traversals are context-aware (for example, bound-variable handling in set aggregation).

## SCQ Sizing

SCQ sizes are computed from expression structure and propagation-delay properties, then attached to
nodes before assembly (`compute_scq_sizes`).

The resulting queue sizes drive temporal memory allocation in generated configuration instructions.

## Engine Assignment and Atomics

CPT expressions are assigned to either:

- Booleanizer engine (BZ), or
- Temporal Logic engine (TL)

Any BZ expression consumed by TL is treated as an atomic interface value. These interfaces are
identified by `compute_atomics` and later emitted as coordinated BZ/TL instructions during assembly.