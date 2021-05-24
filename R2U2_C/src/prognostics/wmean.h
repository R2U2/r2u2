/*
 * File: wmean.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __WMEAN_H__
#define __WMEAN_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void b_wmean(const emxArray_real_T *X, const emxArray_real_T *w,
                    emxArray_real_T *mX);
extern void c_wmean(const emxArray_real_T *X, const emxArray_real_T *w, double
                    mX_data[], int mX_size[1]);
extern void wmean(const emxArray_real_T *X, const emxArray_real_T *w,
                  emxArray_real_T *mX);

#endif

/*
 * File trailer for wmean.h
 *
 * [EOF]
 */
