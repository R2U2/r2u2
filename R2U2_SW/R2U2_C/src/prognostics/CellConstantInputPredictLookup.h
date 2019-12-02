/*
 * File: CellConstantInputPredictLookup.h
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

#ifndef __CELLCONSTANTINPUTPREDICTLOOKUP_H__
#define __CELLCONSTANTINPUTPREDICTLOOKUP_H__

/* Include Files */
#include <math.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include "rt_nonfinite.h"
#include "rtwtypes.h"
#include "BHM_types.h"

/* Function Declarations */
extern void CellConstantInputPredictLookup(double t0, emxArray_real_T *X, const
  emxArray_real_T *w, const emxArray_real_T *u, char input, emxArray_real_T *EOL,
  emxArray_real_T *RUL, emxArray_real_T *W);

#endif

/*
 * File trailer for CellConstantInputPredictLookup.h
 *
 * [EOF]
 */
