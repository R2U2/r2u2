/*
 * File: UKFStep.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __UKFSTEP_H__
#define __UKFSTEP_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void UKFStep(double t, double newT, const emxArray_real_T *xOld, const
                    emxArray_real_T *POld, const emxArray_real_T *uOld, const
                    emxArray_real_T *u, const emxArray_real_T *z, const
                    emxArray_real_T *modelVariance, const emxArray_real_T
                    *sensorVariance, emxArray_real_T *x, emxArray_real_T *P,
                    emxArray_real_T *zhat);

#endif

/*
 * File trailer for UKFStep.h
 *
 * [EOF]
 */
