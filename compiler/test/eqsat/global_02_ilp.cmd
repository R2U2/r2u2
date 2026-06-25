parse_mltl global_02.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%scq "

optimize_eqsat --check-equiv --extraction-method ilp --no-multi-arity

compute_scq_sizes
print_stats "%scq\n"
