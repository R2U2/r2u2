parse_mltl not_not.mltl
type_check
compute_atomics 

compute_scq_sizes
#print_stats "%S "

set_debug
optimize_eqsat --check-equiv --extraction-method optimal

compute_scq_sizes
#print_stats "%S\n"
