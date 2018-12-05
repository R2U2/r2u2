/*
 * File: wcov.c
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
#include "wcov.h"
#include "BHM_emxutil.h"
#include "wmean.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Pxx = wcov(X,w,alpha,beta)
 *  weighted covariance calculation
 *  if alpha/beta are given, then the data is assumed to be sigma points, and the
 *  1/(1-sum(w.^2)) factor will not be applied.
 *
 *  X should be (nx x n) and w should be (n x 1). If X is a vector,
 *  then X and w may be either row or column vectors.
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *w
 *                double Pxx_data[]
 *                int Pxx_size[2]
 * Return Type  : void
 */
void b_wcov(const emxArray_real_T *X, const emxArray_real_T *w, double Pxx_data[],
            int Pxx_size[2])
{
  emxArray_real_T *newX;
  emxArray_real_T *b_X;
  int i27;
  int loop_ub;
  int y;
  emxArray_real_T *W;
  emxArray_real_T *b_w;
  double w_data_idx_0;
  emxArray_real_T *r965;
  int mX_size_idx_0;
  double mX_data[2];
  int b_y;
  int i28;
  int i29;
  emxArray_real_T *b_W;
  emxArray_real_T *r966;
  int b_loop_ub;
  double newX_data[2];
  double tmp_data[2];
  double b_newX_data[2];
  emxArray_real_T *r967;
  emxArray_real_T *r968;

  /*  make sure that if X is a vector, then both X and w are row vectors */
  emxInit_real_T(&newX, 2);
  if (X->size[1] == 1) {
    emxInit_real_T(&b_X, 2);

    /*  then X is a column vector, make it a row vector */
    i27 = b_X->size[0] * b_X->size[1];
    b_X->size[0] = X->size[1];
    b_X->size[1] = 2;
    emxEnsureCapacity((emxArray__common *)b_X, i27, (int)sizeof(double));
    for (i27 = 0; i27 < 2; i27++) {
      loop_ub = X->size[1];
      for (y = 0; y < loop_ub; y++) {
        b_X->data[y + b_X->size[0] * i27] = X->data[i27 + X->size[0] * y];
      }
    }

    i27 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = 2;
    emxEnsureCapacity((emxArray__common *)newX, i27, (int)sizeof(double));
    for (i27 = 0; i27 < 2; i27++) {
      y = 0;
      while (y <= 0) {
        newX->data[newX->size[0] * i27] = b_X->data[i27];
        y = 1;
      }
    }

    emxFree_real_T(&b_X);
  } else {
    i27 = newX->size[0] * newX->size[1];
    newX->size[0] = 2;
    newX->size[1] = X->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i27, (int)sizeof(double));
    loop_ub = X->size[0] * X->size[1];
    for (i27 = 0; i27 < loop_ub; i27++) {
      newX->data[i27] = X->data[i27];
    }
  }

  emxInit_real_T(&W, 2);
  if (w->size[1] == 1) {
    b_emxInit_real_T(&b_w, 1);

    /*  then w is a column vector, make it a row vector */
    i27 = b_w->size[0];
    b_w->size[0] = w->size[1];
    emxEnsureCapacity((emxArray__common *)b_w, i27, (int)sizeof(double));
    loop_ub = w->size[1];
    for (i27 = 0; i27 < loop_ub; i27++) {
      b_w->data[i27] = w->data[w->size[0] * i27];
    }

    w_data_idx_0 = b_w->data[0];
    i27 = W->size[0] * W->size[1];
    W->size[0] = 1;
    W->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)W, i27, (int)sizeof(double));
    W->data[0] = w_data_idx_0;
    emxFree_real_T(&b_w);
  } else {
    i27 = W->size[0] * W->size[1];
    W->size[0] = 1;
    W->size[1] = w->size[1];
    emxEnsureCapacity((emxArray__common *)W, i27, (int)sizeof(double));
    loop_ub = w->size[0] * w->size[1];
    for (i27 = 0; i27 < loop_ub; i27++) {
      W->data[i27] = w->data[i27];
    }
  }

  emxInit_real_T(&r965, 2);
  b_wmean(newX, W, r965);
  mX_size_idx_0 = r965->size[0];
  loop_ub = r965->size[0] * r965->size[1];
  for (i27 = 0; i27 < loop_ub; i27++) {
    mX_data[i27] = r965->data[i27];
  }

  emxFree_real_T(&r965);
  if (mX_size_idx_0 >= 1) {
    y = mX_size_idx_0;
  } else {
    y = 1;
  }

  if (mX_size_idx_0 >= 1) {
    b_y = mX_size_idx_0;
  } else {
    b_y = 1;
  }

  if (0 == mX_size_idx_0) {
    i28 = 0;
  } else {
    i28 = y;
  }

  if (0 == mX_size_idx_0) {
    i29 = 0;
  } else {
    i29 = b_y;
  }

  loop_ub = i28 * i29;
  for (i27 = 0; i27 < loop_ub; i27++) {
    Pxx_data[i27] = 0.0;
  }

  mX_size_idx_0 = 0;
  b_emxInit_real_T(&b_W, 1);
  emxInit_real_T(&r966, 2);
  while (mX_size_idx_0 <= newX->size[1] - 1) {
    loop_ub = newX->size[0];
    b_loop_ub = newX->size[0];
    for (i27 = 0; i27 < b_loop_ub; i27++) {
      newX_data[i27] = newX->data[i27 + newX->size[0] * mX_size_idx_0];
    }

    for (i27 = 0; i27 < loop_ub; i27++) {
      tmp_data[i27] = newX_data[i27];
    }

    b_loop_ub = newX->size[0];
    y = newX->size[0];
    w_data_idx_0 = W->data[mX_size_idx_0];
    b_y = newX->size[0];
    for (i27 = 0; i27 < b_y; i27++) {
      newX_data[i27] = newX->data[i27 + newX->size[0] * mX_size_idx_0];
    }

    for (i27 = 0; i27 < b_loop_ub; i27++) {
      b_newX_data[i27] = newX_data[i27];
    }

    i27 = b_W->size[0];
    b_W->size[0] = y;
    emxEnsureCapacity((emxArray__common *)b_W, i27, (int)sizeof(double));
    for (i27 = 0; i27 < y; i27++) {
      b_W->data[i27] = w_data_idx_0 * (b_newX_data[i27] - mX_data[i27]);
    }

    i27 = r966->size[0] * r966->size[1];
    r966->size[0] = 1;
    r966->size[1] = loop_ub;
    emxEnsureCapacity((emxArray__common *)r966, i27, (int)sizeof(double));
    for (i27 = 0; i27 < loop_ub; i27++) {
      r966->data[r966->size[0] * i27] = tmp_data[i27] - mX_data[i27];
    }

    Pxx_size[0] = b_W->size[0];
    loop_ub = b_W->size[0];
    for (i27 = 0; i27 < loop_ub; i27++) {
      b_loop_ub = r966->size[1];
      for (y = 0; y < b_loop_ub; y++) {
        w_data_idx_0 = b_W->data[i27] * r966->data[r966->size[0] * y];
        Pxx_data[i27 + Pxx_size[0] * y] += w_data_idx_0;
      }
    }

    mX_size_idx_0++;
  }

  emxFree_real_T(&r966);
  emxFree_real_T(&b_W);
  emxFree_real_T(&W);
  loop_ub = newX->size[0];
  b_loop_ub = newX->size[0];
  for (i27 = 0; i27 < b_loop_ub; i27++) {
    newX_data[i27] = newX->data[i27];
  }

  for (i27 = 0; i27 < loop_ub; i27++) {
    tmp_data[i27] = newX_data[i27];
  }

  b_loop_ub = newX->size[0];
  y = newX->size[0];
  b_y = newX->size[0];
  for (i27 = 0; i27 < b_y; i27++) {
    newX_data[i27] = newX->data[i27];
  }

  emxFree_real_T(&newX);
  for (i27 = 0; i27 < b_loop_ub; i27++) {
    b_newX_data[i27] = newX_data[i27];
  }

  b_emxInit_real_T(&r967, 1);
  emxInit_real_T(&r968, 2);
  i27 = r967->size[0];
  r967->size[0] = y;
  emxEnsureCapacity((emxArray__common *)r967, i27, (int)sizeof(double));
  for (i27 = 0; i27 < y; i27++) {
    r967->data[i27] = 0.0 * (b_newX_data[i27] - mX_data[i27]);
  }

  i27 = r968->size[0] * r968->size[1];
  r968->size[0] = 1;
  r968->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)r968, i27, (int)sizeof(double));
  for (i27 = 0; i27 < loop_ub; i27++) {
    r968->data[r968->size[0] * i27] = tmp_data[i27] - mX_data[i27];
  }

  Pxx_size[0] = r967->size[0];
  Pxx_size[1] = r968->size[1];
  loop_ub = r967->size[0];
  for (i27 = 0; i27 < loop_ub; i27++) {
    b_loop_ub = r968->size[1];
    for (y = 0; y < b_loop_ub; y++) {
      w_data_idx_0 = r967->data[i27] * r968->data[r968->size[0] * y];
      Pxx_data[i27 + Pxx_size[0] * y] += w_data_idx_0;
    }
  }

  emxFree_real_T(&r968);
  emxFree_real_T(&r967);
}

/*
 * Pxx = wcov(X,w,alpha,beta)
 *  weighted covariance calculation
 *  if alpha/beta are given, then the data is assumed to be sigma points, and the
 *  1/(1-sum(w.^2)) factor will not be applied.
 *
 *  X should be (nx x n) and w should be (n x 1). If X is a vector,
 *  then X and w may be either row or column vectors.
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *w
 *                emxArray_real_T *Pxx
 * Return Type  : void
 */
void wcov(const emxArray_real_T *X, const emxArray_real_T *w, emxArray_real_T
          *Pxx)
{
  emxArray_real_T *newX;
  emxArray_real_T *b_X;
  int i17;
  int loop_ub;
  int b_loop_ub;
  int n;
  int unnamed_idx_1;
  emxArray_real_T *W;
  emxArray_real_T *b_w;
  double w_data_idx_0;
  emxArray_real_T *mX;
  int i;
  emxArray_real_T *r793;
  emxArray_real_T *b_newX;
  emxArray_real_T *c_newX;
  emxArray_real_T *d_newX;
  emxArray_real_T *b_W;
  emxArray_real_T *e_newX;
  emxArray_real_T *f_newX;
  emxArray_real_T *g_newX;
  emxArray_real_T *h_newX;
  emxArray_real_T *r794;
  emxArray_real_T *i_newX;

  /*  make sure that if X is a vector, then both X and w are row vectors */
  emxInit_real_T(&newX, 2);
  if (X->size[1] == 1) {
    emxInit_real_T(&b_X, 2);

    /*  then X is a column vector, make it a row vector */
    i17 = b_X->size[0] * b_X->size[1];
    b_X->size[0] = X->size[1];
    b_X->size[1] = X->size[0];
    emxEnsureCapacity((emxArray__common *)b_X, i17, (int)sizeof(double));
    loop_ub = X->size[0];
    for (i17 = 0; i17 < loop_ub; i17++) {
      b_loop_ub = X->size[1];
      for (n = 0; n < b_loop_ub; n++) {
        b_X->data[n + b_X->size[0] * i17] = X->data[i17 + X->size[0] * n];
      }
    }

    unnamed_idx_1 = X->size[0];
    i17 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = unnamed_idx_1;
    emxEnsureCapacity((emxArray__common *)newX, i17, (int)sizeof(double));
    for (i17 = 0; i17 < unnamed_idx_1; i17++) {
      n = 0;
      while (n <= 0) {
        newX->data[newX->size[0] * i17] = b_X->data[i17];
        n = 1;
      }
    }

    emxFree_real_T(&b_X);
  } else {
    i17 = newX->size[0] * newX->size[1];
    newX->size[0] = X->size[0];
    newX->size[1] = X->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i17, (int)sizeof(double));
    loop_ub = X->size[0] * X->size[1];
    for (i17 = 0; i17 < loop_ub; i17++) {
      newX->data[i17] = X->data[i17];
    }
  }

  emxInit_real_T(&W, 2);
  if (w->size[1] == 1) {
    b_emxInit_real_T(&b_w, 1);

    /*  then w is a column vector, make it a row vector */
    i17 = b_w->size[0];
    b_w->size[0] = w->size[1];
    emxEnsureCapacity((emxArray__common *)b_w, i17, (int)sizeof(double));
    loop_ub = w->size[1];
    for (i17 = 0; i17 < loop_ub; i17++) {
      b_w->data[i17] = w->data[w->size[0] * i17];
    }

    w_data_idx_0 = b_w->data[0];
    i17 = W->size[0] * W->size[1];
    W->size[0] = 1;
    W->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)W, i17, (int)sizeof(double));
    W->data[0] = w_data_idx_0;
    emxFree_real_T(&b_w);
  } else {
    i17 = W->size[0] * W->size[1];
    W->size[0] = 1;
    W->size[1] = w->size[1];
    emxEnsureCapacity((emxArray__common *)W, i17, (int)sizeof(double));
    loop_ub = w->size[0] * w->size[1];
    for (i17 = 0; i17 < loop_ub; i17++) {
      W->data[i17] = w->data[i17];
    }
  }

  emxInit_real_T(&mX, 2);
  b_wmean(newX, W, mX);
  unnamed_idx_1 = mX->size[0];
  if (unnamed_idx_1 >= 1) {
  } else {
    unnamed_idx_1 = 1;
  }

  if (0 == mX->size[0]) {
    n = 0;
  } else {
    n = unnamed_idx_1;
  }

  unnamed_idx_1 = mX->size[0];
  if (unnamed_idx_1 >= 1) {
  } else {
    unnamed_idx_1 = 1;
  }

  if (0 == mX->size[0]) {
    unnamed_idx_1 = 0;
  }

  i17 = Pxx->size[0] * Pxx->size[1];
  Pxx->size[0] = n;
  Pxx->size[1] = unnamed_idx_1;
  emxEnsureCapacity((emxArray__common *)Pxx, i17, (int)sizeof(double));
  loop_ub = n * unnamed_idx_1;
  for (i17 = 0; i17 < loop_ub; i17++) {
    Pxx->data[i17] = 0.0;
  }

  i = 0;
  emxInit_real_T(&r793, 2);
  b_emxInit_real_T(&b_newX, 1);
  b_emxInit_real_T(&c_newX, 1);
  emxInit_real_T(&d_newX, 2);
  b_emxInit_real_T(&b_W, 1);
  emxInit_real_T(&e_newX, 2);
  while (i <= newX->size[1] - 1) {
    loop_ub = newX->size[0];
    b_loop_ub = newX->size[0];
    i17 = b_newX->size[0];
    b_newX->size[0] = b_loop_ub;
    emxEnsureCapacity((emxArray__common *)b_newX, i17, (int)sizeof(double));
    for (i17 = 0; i17 < b_loop_ub; i17++) {
      b_newX->data[i17] = newX->data[i17 + newX->size[0] * i];
    }

    i17 = r793->size[0] * r793->size[1];
    r793->size[0] = loop_ub;
    r793->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)r793, i17, (int)sizeof(double));
    for (i17 = 0; i17 < loop_ub; i17++) {
      r793->data[i17] = b_newX->data[i17];
    }

    loop_ub = newX->size[0];
    b_loop_ub = newX->size[0];
    w_data_idx_0 = W->data[i];
    unnamed_idx_1 = r793->size[0];
    n = newX->size[0];
    i17 = c_newX->size[0];
    c_newX->size[0] = n;
    emxEnsureCapacity((emxArray__common *)c_newX, i17, (int)sizeof(double));
    for (i17 = 0; i17 < n; i17++) {
      c_newX->data[i17] = newX->data[i17 + newX->size[0] * i];
    }

    i17 = d_newX->size[0] * d_newX->size[1];
    d_newX->size[0] = loop_ub;
    d_newX->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)d_newX, i17, (int)sizeof(double));
    for (i17 = 0; i17 < loop_ub; i17++) {
      d_newX->data[i17] = c_newX->data[i17];
    }

    i17 = b_W->size[0];
    b_W->size[0] = unnamed_idx_1;
    emxEnsureCapacity((emxArray__common *)b_W, i17, (int)sizeof(double));
    for (i17 = 0; i17 < unnamed_idx_1; i17++) {
      b_W->data[i17] = w_data_idx_0 * (r793->data[i17] - mX->data[i17]);
    }

    i17 = e_newX->size[0] * e_newX->size[1];
    e_newX->size[0] = 1;
    e_newX->size[1] = b_loop_ub;
    emxEnsureCapacity((emxArray__common *)e_newX, i17, (int)sizeof(double));
    for (i17 = 0; i17 < b_loop_ub; i17++) {
      e_newX->data[e_newX->size[0] * i17] = d_newX->data[i17] - mX->data[i17];
    }

    i17 = Pxx->size[0] * Pxx->size[1];
    Pxx->size[0] = b_W->size[0];
    Pxx->size[1] = e_newX->size[1];
    emxEnsureCapacity((emxArray__common *)Pxx, i17, (int)sizeof(double));
    loop_ub = b_W->size[0];
    for (i17 = 0; i17 < loop_ub; i17++) {
      b_loop_ub = e_newX->size[1];
      for (n = 0; n < b_loop_ub; n++) {
        w_data_idx_0 = b_W->data[i17] * e_newX->data[e_newX->size[0] * n];
        Pxx->data[i17 + Pxx->size[0] * n] += w_data_idx_0;
      }
    }

    i++;
  }

  emxFree_real_T(&e_newX);
  emxFree_real_T(&b_W);
  emxFree_real_T(&d_newX);
  emxFree_real_T(&c_newX);
  emxFree_real_T(&b_newX);
  emxFree_real_T(&W);
  b_emxInit_real_T(&f_newX, 1);
  loop_ub = newX->size[0];
  b_loop_ub = newX->size[0];
  i17 = f_newX->size[0];
  f_newX->size[0] = b_loop_ub;
  emxEnsureCapacity((emxArray__common *)f_newX, i17, (int)sizeof(double));
  for (i17 = 0; i17 < b_loop_ub; i17++) {
    f_newX->data[i17] = newX->data[i17];
  }

  i17 = r793->size[0] * r793->size[1];
  r793->size[0] = loop_ub;
  r793->size[1] = 1;
  emxEnsureCapacity((emxArray__common *)r793, i17, (int)sizeof(double));
  for (i17 = 0; i17 < loop_ub; i17++) {
    r793->data[i17] = f_newX->data[i17];
  }

  emxFree_real_T(&f_newX);
  b_emxInit_real_T(&g_newX, 1);
  loop_ub = newX->size[0];
  b_loop_ub = newX->size[0];
  unnamed_idx_1 = r793->size[0];
  n = newX->size[0];
  i17 = g_newX->size[0];
  g_newX->size[0] = n;
  emxEnsureCapacity((emxArray__common *)g_newX, i17, (int)sizeof(double));
  for (i17 = 0; i17 < n; i17++) {
    g_newX->data[i17] = newX->data[i17];
  }

  emxFree_real_T(&newX);
  emxInit_real_T(&h_newX, 2);
  i17 = h_newX->size[0] * h_newX->size[1];
  h_newX->size[0] = loop_ub;
  h_newX->size[1] = 1;
  emxEnsureCapacity((emxArray__common *)h_newX, i17, (int)sizeof(double));
  for (i17 = 0; i17 < loop_ub; i17++) {
    h_newX->data[i17] = g_newX->data[i17];
  }

  emxFree_real_T(&g_newX);
  b_emxInit_real_T(&r794, 1);
  emxInit_real_T(&i_newX, 2);
  i17 = r794->size[0];
  r794->size[0] = unnamed_idx_1;
  emxEnsureCapacity((emxArray__common *)r794, i17, (int)sizeof(double));
  for (i17 = 0; i17 < unnamed_idx_1; i17++) {
    r794->data[i17] = 0.0 * (r793->data[i17] - mX->data[i17]);
  }

  emxFree_real_T(&r793);
  i17 = i_newX->size[0] * i_newX->size[1];
  i_newX->size[0] = 1;
  i_newX->size[1] = b_loop_ub;
  emxEnsureCapacity((emxArray__common *)i_newX, i17, (int)sizeof(double));
  for (i17 = 0; i17 < b_loop_ub; i17++) {
    i_newX->data[i_newX->size[0] * i17] = h_newX->data[i17] - mX->data[i17];
  }

  emxFree_real_T(&h_newX);
  emxFree_real_T(&mX);
  i17 = Pxx->size[0] * Pxx->size[1];
  Pxx->size[0] = r794->size[0];
  Pxx->size[1] = i_newX->size[1];
  emxEnsureCapacity((emxArray__common *)Pxx, i17, (int)sizeof(double));
  loop_ub = r794->size[0];
  for (i17 = 0; i17 < loop_ub; i17++) {
    b_loop_ub = i_newX->size[1];
    for (n = 0; n < b_loop_ub; n++) {
      w_data_idx_0 = r794->data[i17] * i_newX->data[i_newX->size[0] * n];
      Pxx->data[i17 + Pxx->size[0] * n] += w_data_idx_0;
    }
  }

  emxFree_real_T(&i_newX);
  emxFree_real_T(&r794);
}

/*
 * File trailer for wcov.c
 *
 * [EOF]
 */
