/*
 * File: UKFInitialize.c
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
#include "BHM_emxutil.h"
#include "OutputEqnUKF.h"
#include <stdio.h>

/* Function Definitions */

/*
 * initialize sizes
 * Arguments    : double t0
 *                double I
 *                double V
 *                double T
 *                const emxArray_real_T *modelVariance
 *                emxArray_real_T *x0
 *                double *u0
 *                double z0[2]
 *                emxArray_real_T *P0
 * Return Type  : void
 */
void UKFInitialize(double t0, double I, double V, double T, const
                   emxArray_real_T *modelVariance, emxArray_real_T *x0, double
                   *u0, double z0[2], emxArray_real_T *P0)
{
  double dv0[8];
  int i19;
  int unnamed_idx_0;
  int unnamed_idx_1;
  (void)t0;
  getInitialBatteryState(I, V, T, dv0);
  i19 = x0->size[0];
  x0->size[0] = 8;
  emxEnsureCapacity((emxArray__common *)x0, i19, (int)sizeof(double));
  for (i19 = 0; i19 < 8; i19++) {
    x0->data[i19] = dv0[i19];
  }

  *u0 = I;
  OutputEqnUKF(x0->data, z0);
  unnamed_idx_0 = modelVariance->size[1];
  unnamed_idx_1 = modelVariance->size[1];
  i19 = P0->size[0] * P0->size[1];
  P0->size[0] = unnamed_idx_0;
  emxEnsureCapacity((emxArray__common *)P0, i19, (int)sizeof(double));
  i19 = P0->size[0] * P0->size[1];
  P0->size[1] = unnamed_idx_1;
  emxEnsureCapacity((emxArray__common *)P0, i19, (int)sizeof(double));
  unnamed_idx_0 *= unnamed_idx_1;
  for (i19 = 0; i19 < unnamed_idx_0; i19++) {
    P0->data[i19] = 0.0;
  }

  for (unnamed_idx_0 = 0; unnamed_idx_0 + 1 <= modelVariance->size[1];
       unnamed_idx_0++) {
    P0->data[unnamed_idx_0 + P0->size[0] * unnamed_idx_0] = modelVariance->
      data[unnamed_idx_0];
  }

  /* [X,W] = Observers.computeSigmaPoints(x,Q,'symmetric',[-5 0],1); */
  /* sigmaPoints = struct('x',X,'w',W,'z',Battery.OutputEqnUKF(t0,X,u0,0)); */
}

/*
 * File trailer for UKFInitialize.c
 *
 * [EOF]
 */
