parse_mltl test.mltl
type_check
compute_atomics 

compute_scq_sizes
print_stats "%scq "

write_eqsat_encoding test.egg
set_debug
optimize_eqsat --check-equiv --extraction-method optimal --no-multi-arity

compute_scq_sizes
print_stats "%scq\n"
