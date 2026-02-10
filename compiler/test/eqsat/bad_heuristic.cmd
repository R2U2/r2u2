parse_mltl bad_heuristic.mltl
type_check
compute_atomics 

optimize_cse
compute_scq_sizes
print_stats "%scq "

optimize_eqsat --check-equiv --extraction-method heuristic

optimize_cse
compute_scq_sizes
print_stats "%scq\n"
