parse_c2po basic.c2po
parse_map ../default.map
type_check
desugar
optimize_cse
compute_atomics
compute_scq_sizes
assemble /dev/null --print