/*
 * File: computeSOCEstimate.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __COMPUTESOCESTIMATE_H__
#define __COMPUTESOCESTIMATE_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void computeSOCEstimate(const emxArray_real_T *muX, const emxArray_real_T
  *PX, emxArray_real_T *SOCMean, double SOCVariance_data[], int
  SOCVariance_size[2]);

#endif

/*
 * File trailer for computeSOCEstimate.h
 *
 * [EOF]
 */
