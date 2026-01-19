parse_mltl future_until_01.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%S "

optimize_eqsat --check-equiv --extraction-method optimal

compute_scq_sizes
print_stats "%S\n"
