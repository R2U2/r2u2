parse_c2po equality.c2po
parse_map ../default.map
type_check
optimize_rewrites
optimize_cse
assemble /dev/null --print