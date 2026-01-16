parse_mltl and_global_02.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%S "

optimize_eqsat --check-equiv

compute_scq_sizes
print_stats "%S\n"
