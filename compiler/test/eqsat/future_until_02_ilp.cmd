parse_mltl future_until_02.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%scq "

optimize_eqsat --extraction-method ilp

compute_scq_sizes
print_stats "%scq\n"
