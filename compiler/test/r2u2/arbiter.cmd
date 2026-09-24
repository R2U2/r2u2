parse_c2po arbiter.c2po
enable_booleanizer
type_check
desugar
generate_map
assemble arbiter.bin
run_r2u2 arbiter.bin arbiter.csv --print
