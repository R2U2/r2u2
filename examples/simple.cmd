parse_c2po simple.c2po
parse_map simple.map
type_check
desugar
optimize_rewrites
optimize_cse
remove_extended_operators
multi_operators_to_binary
assemble --print spec.bin
