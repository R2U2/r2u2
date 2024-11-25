#ifndef R2U2_ENGINES_COMPARE_H
#define R2U2_ENGINES_COMPARE_H

#include "r2u2.h"

#include "internals/types.h"

r2u2_bool r2u2_at_compare_int_eq(r2u2_int a, r2u2_int b);
r2u2_bool r2u2_at_compare_int_neq(r2u2_int a, r2u2_int b);
r2u2_bool r2u2_at_compare_int_lt(r2u2_int a, r2u2_int b);
r2u2_bool r2u2_at_compare_int_leq(r2u2_int a, r2u2_int b);
r2u2_bool r2u2_at_compare_int_gt(r2u2_int a, r2u2_int b);
r2u2_bool r2u2_at_compare_int_geq(r2u2_int a, r2u2_int b);
r2u2_bool r2u2_at_compare_float_eq(r2u2_float a, r2u2_float b, r2u2_float epsilon);
r2u2_bool r2u2_at_compare_float_neq(r2u2_float a, r2u2_float b, r2u2_float epsilon);
r2u2_bool r2u2_at_compare_float_lt(r2u2_float a, r2u2_float b, r2u2_float epsilon);
r2u2_bool r2u2_at_compare_float_leq(r2u2_float a, r2u2_float b, r2u2_float epsilon);
r2u2_bool r2u2_at_compare_float_gt(r2u2_float a, r2u2_float b, r2u2_float epsilon);
r2u2_bool r2u2_at_compare_float_geq(r2u2_float a, r2u2_float b, r2u2_float epsilon);

extern r2u2_bool (*r2u2_at_compare_int[])(r2u2_int, r2u2_int);
extern r2u2_bool (*r2u2_at_compare_float[])(r2u2_float, r2u2_float, r2u2_float);

#endif /* R2U2_ENGINES_AT_COMPARE_H */
