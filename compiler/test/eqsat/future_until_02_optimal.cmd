parse_mltl future_until_02.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%S "

optimize_eqsat --extraction-method optimal

compute_scq_sizes
print_stats "%S\n"
