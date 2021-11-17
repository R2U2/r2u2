#include "at_compare.h"

bool compare_int_eq(int32_t a, int32_t b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d == %d = %d \n", a, b, (a == b));
  return a == b;
}

bool compare_int_neq(int32_t a, int32_t b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d != %d = %d \n", a, b, (a != b));
  return a != b;
}

bool compare_int_lt(int32_t a, int32_t b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d < %d = %d \n", a, b, (a < b));
  return a < b;
}

bool compare_int_leq(int32_t a, int32_t b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d <= %d = %d \n", a, b, (a <= b));
  return a <= b;
}

bool compare_int_gt(int32_t a, int32_t b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d > %d = %d \n", a, b, (a > b));
  return a > b;
}

bool compare_int_geq(int32_t a, int32_t b)
{
  R2U2_DEBUG_PRINT("\t\tInt Compare: %d >= %d = %d \n", a, b, (a >= b));
  return a >= b;
}

bool compare_double_eq(double a, double b)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf == %lf = %d \n", a, b, (a == b));
  return a == b;
}

bool compare_double_neq(double a, double b)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf != %lf = %d \n", a, b, (a != b));
  return a != b;
}
bool compare_double_lt(double a, double b)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf < %lf = %d \n", a, b, (a < b));
  return a < b;
}

bool compare_double_leq(double a, double b)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf <= %lf = %d \n", a, b, (a <= b));
  return a <= b;
}

bool compare_double_gt(double a, double b)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf > %lf = %d \n", a, b, (a > b));
  return a > b;
}

bool compare_double_geq(double a, double b)
{
  R2U2_DEBUG_PRINT("\t\tDub Compare: %lf >= %lf = %d \n", a, b, (a >= b));
  return a >= b;
}

bool (*compare_int[])(int32_t, int32_t) = { compare_int_eq,
    compare_int_neq,
    compare_int_lt,
    compare_int_leq,
    compare_int_gt,
    compare_int_geq };

bool (*compare_double[])(double, double) = { compare_double_eq,
    compare_double_neq,
    compare_double_lt,
    compare_double_leq,
    compare_double_gt,
    compare_double_geq };
