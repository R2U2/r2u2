parse_c2po bz.c2po
enable_booleanizer
type_check
compute_atomics 

compute_scq_sizes
print_stats "%scq "

optimize_eqsat --check-equiv

compute_scq_sizes
print_stats "%scq\n"
