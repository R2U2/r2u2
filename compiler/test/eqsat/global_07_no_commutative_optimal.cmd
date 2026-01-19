parse_mltl global_07.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%S "

optimize_eqsat --check-equiv --no-commutative --extraction-method optimal

compute_scq_sizes
print_stats "%S\n"
