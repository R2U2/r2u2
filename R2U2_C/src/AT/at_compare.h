#ifndef AT_COMPARE_H
#define AT_COMPARE_H

#include "R2U2.h"

#include <stdint.h>
#include <stdbool.h>

bool compare_int_eq(int32_t a, int32_t b);
bool compare_int_neq(int32_t a, int32_t b);
bool compare_int_lt(int32_t a, int32_t b);
bool compare_int_leq(int32_t a, int32_t b);
bool compare_int_gt(int32_t a, int32_t b);
bool compare_int_geq(int32_t a, int32_t b);
bool compare_double_eq(double a, double b, double epsilon);
bool compare_double_neq(double a, double b, double epsilon);
bool compare_double_lt(double a, double b, double epsilon);
bool compare_double_leq(double a, double b, double epsilon);
bool compare_double_gt(double a, double b, double epsilon);
bool compare_double_geq(double a, double b, double epsilon);

extern bool (*compare_int[])(int32_t, int32_t);
extern bool (*compare_double[])(double, double, double);

#endif
