parse_c2po bz_sat_4.c2po
parse_map ../default.map
enable_booleanizer
type_check
desugar
check_sat uflia --print
