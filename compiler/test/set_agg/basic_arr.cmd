parse_c2po basic_arr.c2po
parse_map ../default.map
enable_booleanizer
type_check
desugar
remove_extended_operators
multi_operators_to_binary
optimize_cse
compute_atomics
compute_scq_sizes
assemble /dev/null --print