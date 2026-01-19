parse_c2po bz.c2po
enable_booleanizer
type_check
compute_atomics 

compute_scq_sizes
print_stats "%S "

optimize_eqsat --check-equiv --extraction-method optimal

compute_scq_sizes
print_stats "%S\n"
