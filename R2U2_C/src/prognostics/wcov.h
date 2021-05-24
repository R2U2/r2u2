/*
 * File: wcov.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __WCOV_H__
#define __WCOV_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void b_wcov(const emxArray_real_T *X, const emxArray_real_T *w, double
                   Pxx_data[], int Pxx_size[2]);
extern void wcov(const emxArray_real_T *X, const emxArray_real_T *w,
                 emxArray_real_T *Pxx);

#endif

/*
 * File trailer for wcov.h
 *
 * [EOF]
 */
