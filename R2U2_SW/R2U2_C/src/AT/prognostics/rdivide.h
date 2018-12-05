/*
 * File: rdivide.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __RDIVIDE_H__
#define __RDIVIDE_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void b_rdivide(const emxArray_real_T *x, const emxArray_real_T *y,
                      emxArray_real_T *z);
extern void c_rdivide(double x, const emxArray_real_T *y, emxArray_real_T *z);
extern void rdivide(const emxArray_real_T *x, double y, emxArray_real_T *z);

#endif

/*
 * File trailer for rdivide.h
 *
 * [EOF]
 */
