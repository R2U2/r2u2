/*
 * File: OutputEqnUKF.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __OUTPUTEQNUKF_H__
#define __OUTPUTEQNUKF_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void OutputEqnUKF(const double X_data[], double Z[2]);
extern void b_OutputEqnUKF(const emxArray_real_T *X, emxArray_real_T *Z);
extern void c_OutputEqnUKF(const emxArray_real_T *X, double Z[2]);

#endif

/*
 * File trailer for OutputEqnUKF.h
 *
 * [EOF]
 */
