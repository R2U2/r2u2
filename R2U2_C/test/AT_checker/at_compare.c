#include "at_compare.h"

uint8_t compare_int_eq(int32_t a, int32_t b)   { return a == b; }
uint8_t compare_int_lt(int32_t a, int32_t b)   { return a <  b; }
uint8_t compare_int_leq(int32_t a, int32_t b)  { return a <= b; } 
uint8_t compare_int_gt(int32_t a, int32_t b)   { return a >  b; }
uint8_t compare_int_geq(int32_t a, int32_t b)  { return a >= b; }
uint8_t compare_double_eq(double a, double b)  { return a == b; }
uint8_t compare_double_lt(double a, double b)  { return a <  b; }
uint8_t compare_double_leq(double a, double b) { return a <= b; }
uint8_t compare_double_gt(double a, double b)  { return a >  b; }
uint8_t compare_double_geq(double a, double b) { return a >= b; }

uint8_t (*compare_int[])(int32_t, int32_t) = {compare_int_eq,
											  compare_int_lt,
											  compare_int_leq,
											  compare_int_gt,
											  compare_int_geq};

uint8_t (*compare_double[])(double, double) = {compare_double_eq,
											   compare_double_lt,
											   compare_double_leq,
											   compare_double_gt,
											   compare_double_geq};
