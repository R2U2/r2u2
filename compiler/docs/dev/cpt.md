# C2PO Parse Tree

The C2PO Parse Tree (CPT) is the primary data structure for C2PO and represents the input
specification throughout compilation. The CPT and its various functions are defined in
`c2po/cpt.py`. CPT node classes represent program structure (e.g., `cpt.StructSection`) or
expression values (e.g., `cpt.Until`). 

Most passes perform a postorder traversal of the CPT, reading or replacing nodes after having
processed that node's children. This traversal can be done over an expression using the `postorder`
generator function, which yields each node of the CPT expression in postorder fashion. Traversals
also usually carry a `cpt.Context` object throughout, that stores information about defined structs,
declared variables, etc.

## DUOQ Sizing

Each node in the final CPT representation requires some memory to store its result during the
execution of R2U2. The exact amount of memory each node requires is determined by the *propagation
delays* of itself and its sibling nodes. For a formal definition and example, see section 2.2 of the
[2023 FMICS paper](https://research.temporallogic.org/papers/JKJRW23.pdf). 

C2PO traverses the final CPT and computes the propagation delays for each node. Since each node
tracks its parents, computing the propagation delays of its siblings is fairly trivial. 

## R2U2 Engines

Each CPT class has an engine type which determines what R2U2 engine will compute that node's value
at runtime. The available engines in R2U2 are the Temporal Logic (TL) Engine, the Booleanizer (BZ),
and Atomic Checkers (AT).

In R2U2, BZ engine nodes can only read from other BZ nodes or the *signals vector* and can write to
the *atomics vector*. TL engine nodes can only read from other TL nodes or the *atomics vector*. As
a result, we mark any BZ nodes that are read from TL nodes as *atomics*. These nodes are computed
during the `compute_atomics` pass in `passes.py`. During assembly, these nodes
emit both a BZ engine instruction to compute their value, a BZ instruction to store its value in the
atomics vector, nd a TL instruction to read it from the atomics vector.