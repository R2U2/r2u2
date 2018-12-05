/*
 * File: log.c
 *
 * MATLAB Coder version            : 2.7
 * C/C++ source code generated on  : 02-Apr-2015 17:30:11
 */

/* Include Files */
#include "rt_nonfinite.h"
#include "CellConstantInputPredict.h"
#include "CellConstantInputPredictLookup.h"
#include "UKFInitialize.h"
#include "UKFStep.h"
#include "computeSOCEstimate.h"
#include "getInitialBatteryState.h"
#include "log.h"
#include "BHM_emxutil.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Arguments    : const emxArray_real_T *x
 *                emxArray_real_T *b_x
 * Return Type  : void
 */
void b_log(const emxArray_real_T *x, emxArray_real_T *b_x)
{
  int i5;
  int loop_ub;
  i5 = b_x->size[0] * b_x->size[1];
  b_x->size[0] = 1;
  b_x->size[1] = x->size[1];
  emxEnsureCapacity((emxArray__common *)b_x, i5, (int)sizeof(double));
  loop_ub = x->size[0] * x->size[1];
  for (i5 = 0; i5 < loop_ub; i5++) {
    b_x->data[i5] = x->data[i5];
  }

  c_log(b_x);
}

/*
 * Arguments    : emxArray_real_T *x
 * Return Type  : void
 */
void c_log(emxArray_real_T *x)
{
  int i30;
  int k;
  i30 = x->size[1];
  for (k = 0; k < i30; k++) {
    x->data[k] = log(x->data[k]);
  }
}

/*
 * File trailer for log.c
 *
 * [EOF]
 */
