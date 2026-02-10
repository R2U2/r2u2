parse_mltl and_until_01.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%scq "

optimize_eqsat --check-equiv --extraction-method optimal

compute_scq_sizes
print_stats "%scq\n"
