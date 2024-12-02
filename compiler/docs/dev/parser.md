# Parser

C2PO uses [SLY](https://sly.readthedocs.io/en/latest/sly.html) to perform parsing. SLY works by
using python annotations to define which parse rules result in calling which function. The parser
takes a `str` as input, then outputs a `cpt.Program`. The parser does some context management in
order to determine what to parse certain symbols as (i.e., whether a symbol is a signal or bound
variable in a set aggregation operator), but in general leaves most context-sensitive tasks to the
type checker.