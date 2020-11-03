#ifndef AT_COMPARE_H
#define AT_COMPARE_H

#include <stdint.h>

uint8_t compare_int_eq(int32_t a, int32_t b);
uint8_t compare_int_lt(int32_t a, int32_t b);
uint8_t compare_int_leq(int32_t a, int32_t b); 
uint8_t compare_int_gt(int32_t a, int32_t b);
uint8_t compare_int_geq(int32_t a, int32_t b);
uint8_t compare_double_eq(double a, double b);
uint8_t compare_double_lt(double a, double b);
uint8_t compare_double_leq(double a, double b); 
uint8_t compare_double_gt(double a, double b);
uint8_t compare_double_geq(double a, double b);

extern uint8_t (*compare_int[])(int32_t, int32_t);
extern uint8_t (*compare_double[])(double, double);

#endif
