/*
 * File: StateEqnUKF.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __STATEEQNUKF_H__
#define __STATEEQNUKF_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void StateEqnUKF(const emxArray_real_T *X, const emxArray_real_T *U,
  double dt, emxArray_real_T *XNew);

#endif

/*
 * File trailer for StateEqnUKF.h
 *
 * [EOF]
 */
