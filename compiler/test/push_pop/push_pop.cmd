parse_c2po push_pop.c2po
parse_map ../default.map
type_check
compute_atomics 
compute_scq_sizes
print_stats "%scq,"

push
optimize_rewrites
compute_scq_sizes
print_stats "%scq,"

pop
print_stats "%scq\n"
