parse_mltl bad_greedy.mltl
type_check
compute_atomics 

optimize_cse
compute_scq_sizes
print_stats "%scq "

optimize_eqsat --check-equiv --extraction-method greedy

optimize_cse
compute_scq_sizes
print_stats "%scq\n"
