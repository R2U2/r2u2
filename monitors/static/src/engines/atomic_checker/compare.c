#include "compare.h"

#include <math.h>

r2u2_bool r2u2_at_compare_int_eq(r2u2_int a, r2u2_int b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d == %d = %d \n", a, b, (a == b));
  return a == b;
}

r2u2_bool r2u2_at_compare_int_neq(r2u2_int a, r2u2_int b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d != %d = %d \n", a, b, (a != b));
  return a != b;
}

r2u2_bool r2u2_at_compare_int_lt(r2u2_int a, r2u2_int b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d < %d = %d \n", a, b, (a < b));
  return a < b;
}

r2u2_bool r2u2_at_compare_int_leq(r2u2_int a, r2u2_int b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d <= %d = %d \n", a, b, (a <= b));
  return a <= b;
}

r2u2_bool r2u2_at_compare_int_gt(r2u2_int a, r2u2_int b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d > %d = %d \n", a, b, (a > b));
  return a > b;
}

r2u2_bool r2u2_at_compare_int_geq(r2u2_int a, r2u2_int b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d >= %d = %d \n", a, b, (a >= b));
  return a >= b;
}

r2u2_bool r2u2_at_compare_float_eq(r2u2_float a, r2u2_float b, r2u2_float epsilon)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: | %lf - %lf | < %lf \n", a, b, epsilon);
  return fabs(a-b) < epsilon;
}

r2u2_bool r2u2_at_compare_float_neq(r2u2_float a, r2u2_float b, r2u2_float epsilon)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: | %lf - %lf | > %lf \n", a, b, epsilon);
  return fabs(a-b) > epsilon;
}
r2u2_bool r2u2_at_compare_float_lt(r2u2_float a, r2u2_float b, r2u2_float epsilon)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf < %lf = %d \n", a, b, (a < b));
  UNUSED(epsilon);
  return a < b;
}

r2u2_bool r2u2_at_compare_float_leq(r2u2_float a, r2u2_float b, r2u2_float epsilon)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf <= %lf = %d \n", a, b, (a <= b));
  UNUSED(epsilon);
  return a <= b;
}

r2u2_bool r2u2_at_compare_float_gt(r2u2_float a, r2u2_float b, r2u2_float epsilon)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf > %lf = %d \n", a, b, (a > b));
  UNUSED(epsilon);
  return a > b;
}

r2u2_bool r2u2_at_compare_float_geq(r2u2_float a, r2u2_float b, r2u2_float epsilon)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf >= %lf = %d \n", a, b, (a >= b));
  UNUSED(epsilon);
  return a >= b;
}

r2u2_bool (*r2u2_at_compare_int[])(r2u2_int, r2u2_int) = { r2u2_at_compare_int_eq,
    r2u2_at_compare_int_neq,
    r2u2_at_compare_int_lt,
    r2u2_at_compare_int_leq,
    r2u2_at_compare_int_gt,
    r2u2_at_compare_int_geq };

r2u2_bool (*r2u2_at_compare_float[])(r2u2_float, r2u2_float, r2u2_float) = { r2u2_at_compare_float_eq,
    r2u2_at_compare_float_neq,
    r2u2_at_compare_float_lt,
    r2u2_at_compare_float_leq,
    r2u2_at_compare_float_gt,
    r2u2_at_compare_float_geq };
