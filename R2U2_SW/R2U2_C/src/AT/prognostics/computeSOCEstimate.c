/*
 * File: computeSOCEstimate.c
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
#include "wmean.h"
#include "rdivide.h"
#include "computeSigmaPoints.h"
#include <stdio.h>

/* Function Definitions */

/*
 * set up sizes
 * Arguments    : const emxArray_real_T *muX
 *                const emxArray_real_T *PX
 *                emxArray_real_T *SOCMean
 *                double SOCVariance_data[]
 *                int SOCVariance_size[2]
 * Return Type  : void
 */
void computeSOCEstimate(const emxArray_real_T *muX, const emxArray_real_T *PX,
  emxArray_real_T *SOCMean, double SOCVariance_data[], int SOCVariance_size[2])
{
  emxArray_real_T *W;
  emxArray_real_T *X;
  emxArray_real_T *b_X;
  int loop_ub;
  int i13;
  emxArray_real_T *SOC;
  emxArray_real_T *newX;
  emxArray_real_T *b_SOC;
  double SOC_data_idx_0;
  emxArray_real_T *b;
  int k;
  int ar;
  emxArray_real_T *c_SOC;
  emxArray_real_T *b_W;
  emxArray_real_T *r788;
  double mX_data[1];
  double Pxx_data[1];
  emxArray_real_T *d_SOC;
  double e_SOC;
  double newX_data_idx_0;
  emxArray_real_T *r789;
  emxInit_real_T(&W, 2);
  emxInit_real_T(&X, 2);
  emxInit_real_T(&b_X, 2);

  /*  use sigma points to compute variance of SOC */
  computeSigmaPoints(muX, PX, 3.0 - (double)muX->size[0], X, W);

  /*  extract states */
  /*  compute apparent SOC */
  /* SOC = qnS/P.qnSMax;	% note that qnSMax already takes the 0.6 factor into consideration */
  /*  compute nominal SOC */
  loop_ub = X->size[1];
  i13 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i13, (int)sizeof(double));
  for (i13 = 0; i13 < loop_ub; i13++) {
    b_X->data[b_X->size[0] * i13] = X->data[3 + X->size[0] * i13] + X->data[2 +
      X->size[0] * i13];
  }

  emxFree_real_T(&X);
  emxInit_real_T(&SOC, 2);
  rdivide(b_X, 7600.0, SOC);

  /*  Compute weighted mean of matrix X with weights w. X should be (nx x n) */
  /*  and w should be a vector. */
  /*  make sure that if X is a vector, then both X and w are column vectors */
  emxFree_real_T(&b_X);
  emxInit_real_T(&newX, 2);
  if (SOC->size[1] == 1) {
    b_emxInit_real_T(&b_SOC, 1);

    /*  then X is a column vector, make it a row vector (for the */
    /*  multiplication) */
    i13 = b_SOC->size[0];
    b_SOC->size[0] = SOC->size[1];
    emxEnsureCapacity((emxArray__common *)b_SOC, i13, (int)sizeof(double));
    loop_ub = SOC->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      b_SOC->data[i13] = SOC->data[SOC->size[0] * i13];
    }

    SOC_data_idx_0 = b_SOC->data[0];
    i13 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)newX, i13, (int)sizeof(double));
    newX->data[0] = SOC_data_idx_0;
    emxFree_real_T(&b_SOC);
  } else {
    i13 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = SOC->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i13, (int)sizeof(double));
    loop_ub = SOC->size[0] * SOC->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      newX->data[i13] = SOC->data[i13];
    }
  }

  b_emxInit_real_T(&b, 1);

  /*  then w is a row vector, make it a column vector */
  i13 = b->size[0];
  b->size[0] = W->size[1];
  emxEnsureCapacity((emxArray__common *)b, i13, (int)sizeof(double));
  loop_ub = W->size[1];
  for (i13 = 0; i13 < loop_ub; i13++) {
    b->data[i13] = W->data[W->size[0] * i13];
  }

  if ((newX->size[1] == 1) || (b->size[0] == 1)) {
    i13 = SOCMean->size[0];
    SOCMean->size[0] = 1;
    emxEnsureCapacity((emxArray__common *)SOCMean, i13, (int)sizeof(double));
    SOCMean->data[0] = 0.0;
    loop_ub = newX->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      SOCMean->data[0] += newX->data[newX->size[0] * i13] * b->data[i13];
    }
  } else {
    k = newX->size[1];
    i13 = SOCMean->size[0];
    SOCMean->size[0] = 1;
    emxEnsureCapacity((emxArray__common *)SOCMean, i13, (int)sizeof(double));
    SOCMean->data[0] = 0.0;
    SOCMean->data[0] = 0.0;
    ar = 0;
    for (loop_ub = 0; loop_ub + 1 <= k; loop_ub++) {
      if (b->data[loop_ub] != 0.0) {
        SOCMean->data[0] += b->data[loop_ub] * newX->data[ar];
      }

      ar++;
    }
  }

  emxFree_real_T(&b);

  /*  Pxx = wcov(X,w,alpha,beta) */
  /*  weighted covariance calculation */
  /*  if alpha/beta are given, then the data is assumed to be sigma points, and the */
  /*  1/(1-sum(w.^2)) factor will not be applied.  */
  /*   */
  /*  X should be (nx x n) and w should be (n x 1). If X is a vector,  */
  /*  then X and w may be either row or column vectors. */
  /*  make sure that if X is a vector, then both X and w are row vectors */
  if (SOC->size[1] == 1) {
    b_emxInit_real_T(&c_SOC, 1);

    /*  then X is a column vector, make it a row vector */
    i13 = c_SOC->size[0];
    c_SOC->size[0] = SOC->size[1];
    emxEnsureCapacity((emxArray__common *)c_SOC, i13, (int)sizeof(double));
    loop_ub = SOC->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      c_SOC->data[i13] = SOC->data[SOC->size[0] * i13];
    }

    SOC_data_idx_0 = c_SOC->data[0];
    i13 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)newX, i13, (int)sizeof(double));
    newX->data[0] = SOC_data_idx_0;
    emxFree_real_T(&c_SOC);
  } else {
    i13 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = SOC->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i13, (int)sizeof(double));
    loop_ub = SOC->size[0] * SOC->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      newX->data[i13] = SOC->data[i13];
    }
  }

  if (W->size[1] == 1) {
    b_emxInit_real_T(&b_W, 1);

    /*  then w is a column vector, make it a row vector */
    i13 = b_W->size[0];
    b_W->size[0] = W->size[1];
    emxEnsureCapacity((emxArray__common *)b_W, i13, (int)sizeof(double));
    loop_ub = W->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      b_W->data[i13] = W->data[W->size[0] * i13];
    }

    SOC_data_idx_0 = b_W->data[0];
    i13 = SOC->size[0] * SOC->size[1];
    SOC->size[0] = 1;
    SOC->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)SOC, i13, (int)sizeof(double));
    SOC->data[0] = SOC_data_idx_0;
    emxFree_real_T(&b_W);
  } else {
    i13 = SOC->size[0] * SOC->size[1];
    SOC->size[0] = 1;
    SOC->size[1] = W->size[1];
    emxEnsureCapacity((emxArray__common *)SOC, i13, (int)sizeof(double));
    loop_ub = W->size[0] * W->size[1];
    for (i13 = 0; i13 < loop_ub; i13++) {
      SOC->data[i13] = W->data[i13];
    }
  }

  emxFree_real_T(&W);
  emxInit_real_T(&r788, 2);
  b_wmean(newX, SOC, r788);
  loop_ub = r788->size[0] * r788->size[1];
  for (i13 = 0; i13 < loop_ub; i13++) {
    mX_data[i13] = r788->data[i13];
  }

  emxFree_real_T(&r788);
  i13 = 0;
  while (i13 <= 0) {
    Pxx_data[0] = 0.0;
    i13 = 1;
  }

  ar = 0;
  b_emxInit_real_T(&d_SOC, 1);
  while (ar <= newX->size[1] - 1) {
    e_SOC = SOC->data[ar];
    SOC_data_idx_0 = newX->data[newX->size[0] * ar];
    newX_data_idx_0 = newX->data[newX->size[0] * ar];
    newX_data_idx_0 -= mX_data[0];
    i13 = d_SOC->size[0];
    d_SOC->size[0] = 1;
    emxEnsureCapacity((emxArray__common *)d_SOC, i13, (int)sizeof(double));
    d_SOC->data[0] = e_SOC * (SOC_data_idx_0 - mX_data[0]);
    loop_ub = d_SOC->size[0];
    for (i13 = 0; i13 < loop_ub; i13++) {
      SOC_data_idx_0 = d_SOC->data[i13] * newX_data_idx_0;
      Pxx_data[i13] += SOC_data_idx_0;
    }

    ar++;
  }

  emxFree_real_T(&d_SOC);
  emxFree_real_T(&SOC);
  b_emxInit_real_T(&r789, 1);
  SOC_data_idx_0 = newX->data[0];
  newX_data_idx_0 = newX->data[0];
  newX_data_idx_0 -= mX_data[0];
  i13 = r789->size[0];
  r789->size[0] = 1;
  emxEnsureCapacity((emxArray__common *)r789, i13, (int)sizeof(double));
  r789->data[0] = 0.0 * (SOC_data_idx_0 - mX_data[0]);
  ar = r789->size[0];
  loop_ub = r789->size[0];
  emxFree_real_T(&newX);
  for (i13 = 0; i13 < loop_ub; i13++) {
    SOC_data_idx_0 = r789->data[i13] * newX_data_idx_0;
    Pxx_data[i13] += SOC_data_idx_0;
  }

  emxFree_real_T(&r789);
  SOCVariance_size[0] = ar;
  SOCVariance_size[1] = 1;
  for (i13 = 0; i13 < ar; i13++) {
    SOCVariance_data[i13] = Pxx_data[i13];
  }

  /*  1,0 here are UKF scaling parameters (no scaling) */
}

/*
 * File trailer for computeSOCEstimate.c
 *
 * [EOF]
 */
