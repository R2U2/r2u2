parse_mltl sat_1.mltl
type_check
check_sat qf_uflia --print
write_smt_encoding sat_1.smt2 qf_uflia
