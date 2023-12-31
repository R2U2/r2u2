# C2PO AST Structure

The AST is the primary data structure for C2PO and represents the input specification throughout compilation. The AST and its various functions are defined in `r2u2/compiler/c2po/ast.py`. AST node classes represent program structure (e.g., `C2POStructSection`) or expression values (e.g., `C2POUntil`). 

Most transforms perform a postorder traversal of the AST, reading or replacing nodes after having processed that node's children. This traversal can be done over an expression using the `postorder` generator function, which yields each node of the AST expression in postorder fashion. Traversals also usually carry a `C2POContext` object throughout, that stores information about defined structs, declared variables, etc.

## Common Sub-expression Elimination
To perform CSE, C2PO traverse the input AST and maintains a `set[str]` of all nodes seen throughout the traversal at a given time. We use the string representation of each node, so this allows us to check for syntactic equivalence fairly efficiently. As the traversal progresses, we check if the current node is in our set, and if so, replace the current node with the node in the set.

## Formula Rewriting
Formula rewriting does a single traversal of the AST and performs the rewrites found in the [2023 FMICS paper](https://research.temporallogic.org/papers/JKJRW23.pdf). Pattern matching is done naively; we check if each node matches each available pattern through one large and nested if-else structure. If a match is found, then the current node is replaced with the valid rewrite.

## SCQ Sizing
Each MLTL node in the final AST representation requires some memory to store its result during the execution of R2U2. The exact amount of memory each node requires is determined by the *propagation delays* of itself and its sibling nodes. For a formal definition and example, see section 2.2 of the [2023 FMICS paper](https://research.temporallogic.org/papers/JKJRW23.pdf). 

C2PO traverses the final AST and computes the propagation delays for each node. Since each node tracks its parents, computing the propagation delays of its siblings is fairly trivial. 