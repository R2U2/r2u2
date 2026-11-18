parse_mltl and_global_01.mltl
type_check
compute_atomics 

compute_scq_sizes
optimize_eqsat --check-equiv

compute_scq_sizes

compile /dev/null
print_stats "%asmnum "
print_stats "%asmbz "
print_stats "%asmtl "
print_stats "%asmtltemp "
print_stats "%asmcg "
print_stats "%asmscq "
print_stats "%asmaliases "
print_stats "%asmsignals "
print_stats "%asmatomics \n"
