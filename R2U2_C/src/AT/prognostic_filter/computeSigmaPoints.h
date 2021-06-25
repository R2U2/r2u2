/*
 * File: computeSigmaPoints.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __COMPUTESIGMAPOINTS_H__
#define __COMPUTESIGMAPOINTS_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void b_computeSigmaPoints(const emxArray_real_T *mx, const
  emxArray_real_T *Pxx, emxArray_real_T *X, emxArray_real_T *W);
extern void computeSigmaPoints(const emxArray_real_T *mx, const emxArray_real_T *
  Pxx, double parameter, emxArray_real_T *X, emxArray_real_T *W);

#endif

/*
 * File trailer for computeSigmaPoints.h
 *
 * [EOF]
 */
