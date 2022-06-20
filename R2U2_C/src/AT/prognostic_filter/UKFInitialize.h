/*
 * File: UKFInitialize.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __UKFINITIALIZE_H__
#define __UKFINITIALIZE_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void UKFInitialize(double t0, double I, double V, double T, const
  emxArray_real_T *modelVariance, emxArray_real_T *x0, double *u0, double z0[2],
  emxArray_real_T *P0);

#endif

/*
 * File trailer for UKFInitialize.h
 *
 * [EOF]
 */
