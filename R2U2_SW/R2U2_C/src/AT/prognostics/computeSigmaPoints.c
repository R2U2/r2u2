/*
 * File: computeSigmaPoints.c
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
#include "computeSigmaPoints.h"
#include "BHM_emxutil.h"
#include "rdivide.h"
#include "repmat.h"
#include <stdio.h>

/* Function Definitions */

/*
 * [X,W,mX,PX] = computeSigmaPoints(mx,Pxx,method,parameter,alpha,sqrtFcn)
 *
 *  Computes sigma points for distribution using specified method and free
 *  parameters. mx is a the mean, and PX is the covariance matrix
 *
 *  Returns sigma points (X,W), and also mean and covariance of sigma points.
 *
 *  Available methods include:
 *
 *  1. 'symmetric' = symmetric sigma points. Free parameters are kappa,
 *  alpha, beta.
 *
 *  2. 'simplex' = minimal skew simplex sigma points. Free parameters are W0,
 *  alpha, beta.
 *
 *  3. 'spherical' = spherical simplex sigma points. Free parameters are
 *  W0, alpha, beta
 *
 *  alpha is optional scaling parameter. Default alpha=1 (no scaling).
 *  sqrtFcn is optional handle to matrix sqrt function to use (sqrtm or
 *  chol). Default is chol.
 * Arguments    : const emxArray_real_T *mx
 *                const emxArray_real_T *Pxx
 *                emxArray_real_T *X
 *                emxArray_real_T *W
 * Return Type  : void
 */
void b_computeSigmaPoints(const emxArray_real_T *mx, const emxArray_real_T *Pxx,
  emxArray_real_T *X, emxArray_real_T *W)
{
  int jj;
  int i22;
  emxArray_real_T *y;
  double ajj;
  int n;
  int b_n;
  int info;
  int colj;
  int j;
  boolean_T exitg1;
  int ix;
  int iy;
  int k;
  int nmj;
  int jjp1;
  int coljp1;
  double c;
  int i23;
  emxArray_real_T *matrixSq;
  emxArray_real_T *r796;
  unsigned int u1;
  emxArray_int32_T *r797;
  emxArray_real_T *b_X;
  emxArray_real_T *c_X;
  emxArray_real_T *b_W;
  emxArray_real_T *r798;

  /*  note: should have a transformSimgaPoints method which given same */
  /*  parameters, because the Pyy calculation depends on alpha and beta. */
  /*  compute sigma points */
  /*  collect parameters */
  /*  compute unscaled sigma points */
  jj = mx->size[0];
  i22 = X->size[0] * X->size[1];
  X->size[0] = jj;
  emxEnsureCapacity((emxArray__common *)X, i22, (int)sizeof(double));
  jj = (int)(2.0 * (double)mx->size[0] + 1.0);
  i22 = X->size[0] * X->size[1];
  X->size[1] = jj;
  emxEnsureCapacity((emxArray__common *)X, i22, (int)sizeof(double));
  jj = mx->size[0] * (int)(2.0 * (double)mx->size[0] + 1.0);
  for (i22 = 0; i22 < jj; i22++) {
    X->data[i22] = 0.0;
  }

  jj = mx->size[0];
  for (i22 = 0; i22 < jj; i22++) {
    X->data[i22] = mx->data[i22];
  }

  emxInit_real_T(&y, 2);
  i22 = y->size[0] * y->size[1];
  y->size[0] = Pxx->size[0];
  y->size[1] = Pxx->size[1];
  emxEnsureCapacity((emxArray__common *)y, i22, (int)sizeof(double));
  ajj = (double)mx->size[0] + -5.0;
  jj = Pxx->size[0] * Pxx->size[1];
  for (i22 = 0; i22 < jj; i22++) {
    y->data[i22] = ajj * Pxx->data[i22];
  }

  n = y->size[1];
  if (y->size[1] == 0) {
  } else {
    b_n = y->size[0];
    info = -1;
    if (y->size[0] == 0) {
    } else {
      colj = 1;
      j = 0;
      exitg1 = false;
      while ((!exitg1) && (j + 1 <= b_n)) {
        jj = (colj + j) - 1;
        ajj = 0.0;
        if (j < 1) {
        } else {
          ix = colj;
          iy = colj;
          for (k = 1; k <= j; k++) {
            ajj += y->data[ix - 1] * y->data[iy - 1];
            ix++;
            iy++;
          }
        }

        ajj = y->data[jj] - ajj;
        if (ajj > 0.0) {
          ajj = sqrt(ajj);
          y->data[jj] = ajj;
          if (j + 1 < b_n) {
            nmj = (b_n - j) - 2;
            jjp1 = jj + b_n;
            coljp1 = colj + b_n;
            if ((j == 0) || (nmj + 1 == 0)) {
            } else {
              iy = jjp1;
              i22 = coljp1 + n * nmj;
              for (jj = coljp1; jj <= i22; jj += n) {
                ix = colj;
                c = 0.0;
                i23 = (jj + j) - 1;
                for (k = jj; k <= i23; k++) {
                  c += y->data[k - 1] * y->data[ix - 1];
                  ix++;
                }

                y->data[iy] += -c;
                iy += n;
              }
            }

            ajj = 1.0 / ajj;
            i22 = (jjp1 + b_n * nmj) + 1;
            for (k = jjp1 + 1; k <= i22; k += b_n) {
              y->data[k - 1] *= ajj;
            }

            colj = coljp1;
          }

          j++;
        } else {
          y->data[jj] = ajj;
          info = j;
          exitg1 = true;
        }
      }
    }

    if (info + 1 == 0) {
      jj = n;
    } else {
      jj = info;
    }

    for (j = 0; j + 1 <= jj; j++) {
      for (k = j + 1; k + 1 <= jj; k++) {
        y->data[k + y->size[0] * j] = 0.0;
      }
    }
  }

  emxInit_real_T(&matrixSq, 2);
  i22 = matrixSq->size[0] * matrixSq->size[1];
  matrixSq->size[0] = y->size[1];
  matrixSq->size[1] = y->size[0];
  emxEnsureCapacity((emxArray__common *)matrixSq, i22, (int)sizeof(double));
  jj = y->size[0];
  for (i22 = 0; i22 < jj; i22++) {
    k = y->size[1];
    for (i23 = 0; i23 < k; i23++) {
      matrixSq->data[i23 + matrixSq->size[0] * i22] = y->data[i22 + y->size[0] *
        i23];
    }
  }

  emxInit_real_T(&r796, 2);
  c_repmat(mx, mx->size[0], r796);
  if (2U > mx->size[0] + 1U) {
    i22 = 0;
  } else {
    i22 = 1;
  }

  jj = r796->size[1];
  for (i23 = 0; i23 < jj; i23++) {
    k = r796->size[0];
    for (jjp1 = 0; jjp1 < k; jjp1++) {
      X->data[jjp1 + X->size[0] * (i22 + i23)] = r796->data[jjp1 + r796->size[0]
        * i23] + matrixSq->data[jjp1 + matrixSq->size[0] * i23];
    }
  }

  c_repmat(mx, mx->size[0], r796);
  u1 = ((unsigned int)mx->size[0] << 1) + 1U;
  if (mx->size[0] + 2U > u1) {
    i22 = 0;
  } else {
    i22 = mx->size[0] + 1;
  }

  jj = r796->size[1];
  for (i23 = 0; i23 < jj; i23++) {
    k = r796->size[0];
    for (jjp1 = 0; jjp1 < k; jjp1++) {
      X->data[jjp1 + X->size[0] * (i22 + i23)] = r796->data[jjp1 + r796->size[0]
        * i23] - matrixSq->data[jjp1 + matrixSq->size[0] * i23];
    }
  }

  emxFree_real_T(&matrixSq);

  /*  compute weights */
  i22 = W->size[0] * W->size[1];
  W->size[0] = 1;
  emxEnsureCapacity((emxArray__common *)W, i22, (int)sizeof(double));
  jj = (int)(2.0 * (double)mx->size[0] + 1.0);
  i22 = W->size[0] * W->size[1];
  W->size[1] = jj;
  emxEnsureCapacity((emxArray__common *)W, i22, (int)sizeof(double));
  jj = (int)(2.0 * (double)mx->size[0] + 1.0);
  for (i22 = 0; i22 < jj; i22++) {
    W->data[i22] = 0.0;
  }

  W->data[0] = -5.0 / ((double)mx->size[0] + -5.0);
  u1 = ((unsigned int)mx->size[0] << 1) + 1U;
  if (2U > u1) {
    i22 = 0;
    i23 = 0;
  } else {
    i22 = 1;
    i23 = (int)u1;
  }

  emxInit_int32_T(&r797, 2);
  jjp1 = r797->size[0] * r797->size[1];
  r797->size[0] = 1;
  r797->size[1] = i23 - i22;
  emxEnsureCapacity((emxArray__common *)r797, jjp1, (int)sizeof(int));
  jj = i23 - i22;
  for (i23 = 0; i23 < jj; i23++) {
    r797->data[r797->size[0] * i23] = i22 + i23;
  }

  ajj = 0.5 / ((double)mx->size[0] + -5.0);
  jj = r797->size[0] * r797->size[1];
  for (i22 = 0; i22 < jj; i22++) {
    W->data[r797->data[i22]] = ajj;
  }

  emxFree_int32_T(&r797);
  b_emxInit_real_T(&b_X, 1);

  /*  scale the sigma points */
  jj = X->size[0];
  i22 = b_X->size[0];
  b_X->size[0] = jj;
  emxEnsureCapacity((emxArray__common *)b_X, i22, (int)sizeof(double));
  for (i22 = 0; i22 < jj; i22++) {
    b_X->data[i22] = X->data[i22];
  }

  b_emxInit_real_T(&c_X, 1);
  c_repmat(b_X, X->size[1], r796);
  jj = X->size[0];
  i22 = c_X->size[0];
  c_X->size[0] = jj;
  emxEnsureCapacity((emxArray__common *)c_X, i22, (int)sizeof(double));
  emxFree_real_T(&b_X);
  for (i22 = 0; i22 < jj; i22++) {
    c_X->data[i22] = X->data[i22];
  }

  c_repmat(c_X, X->size[1], y);
  i22 = X->size[0] * X->size[1];
  X->size[0] = y->size[0];
  X->size[1] = y->size[1];
  emxEnsureCapacity((emxArray__common *)X, i22, (int)sizeof(double));
  jj = y->size[0] * y->size[1];
  emxFree_real_T(&c_X);
  for (i22 = 0; i22 < jj; i22++) {
    X->data[i22] = y->data[i22] + (X->data[i22] - r796->data[i22]);
  }

  emxFree_real_T(&y);
  emxFree_real_T(&r796);

  /*  compute weights */
  if (2 > W->size[1]) {
    i22 = 0;
    i23 = 0;
  } else {
    i22 = 1;
    i23 = W->size[1];
  }

  if (2 > W->size[1]) {
    jjp1 = 0;
  } else {
    jjp1 = 1;
  }

  emxInit_real_T(&b_W, 2);
  jj = b_W->size[0] * b_W->size[1];
  b_W->size[0] = 1;
  b_W->size[1] = i23 - i22;
  emxEnsureCapacity((emxArray__common *)b_W, jj, (int)sizeof(double));
  jj = i23 - i22;
  for (i23 = 0; i23 < jj; i23++) {
    b_W->data[b_W->size[0] * i23] = W->data[i22 + i23];
  }

  emxInit_real_T(&r798, 2);
  rdivide(b_W, 1.0, r798);
  jj = r798->size[1];
  emxFree_real_T(&b_W);
  for (i22 = 0; i22 < jj; i22++) {
    W->data[jjp1 + i22] = r798->data[r798->size[0] * i22];
  }

  emxFree_real_T(&r798);
}

/*
 * [X,W,mX,PX] = computeSigmaPoints(mx,Pxx,method,parameter,alpha,sqrtFcn)
 *
 *  Computes sigma points for distribution using specified method and free
 *  parameters. mx is a the mean, and PX is the covariance matrix
 *
 *  Returns sigma points (X,W), and also mean and covariance of sigma points.
 *
 *  Available methods include:
 *
 *  1. 'symmetric' = symmetric sigma points. Free parameters are kappa,
 *  alpha, beta.
 *
 *  2. 'simplex' = minimal skew simplex sigma points. Free parameters are W0,
 *  alpha, beta.
 *
 *  3. 'spherical' = spherical simplex sigma points. Free parameters are
 *  W0, alpha, beta
 *
 *  alpha is optional scaling parameter. Default alpha=1 (no scaling).
 *  sqrtFcn is optional handle to matrix sqrt function to use (sqrtm or
 *  chol). Default is chol.
 * Arguments    : const emxArray_real_T *mx
 *                const emxArray_real_T *Pxx
 *                double parameter
 *                emxArray_real_T *X
 *                emxArray_real_T *W
 * Return Type  : void
 */
void computeSigmaPoints(const emxArray_real_T *mx, const emxArray_real_T *Pxx,
  double parameter, emxArray_real_T *X, emxArray_real_T *W)
{
  int jj;
  int i14;
  emxArray_real_T *y;
  double ajj;
  int n;
  int b_n;
  int info;
  int colj;
  int j;
  boolean_T exitg1;
  int ix;
  int iy;
  int k;
  int nmj;
  int jjp1;
  int coljp1;
  double c;
  int i15;
  emxArray_real_T *matrixSq;
  emxArray_real_T *r790;
  unsigned int u0;
  emxArray_int32_T *r791;
  emxArray_real_T *b_X;
  emxArray_real_T *c_X;
  emxArray_real_T *b_W;
  emxArray_real_T *r792;

  /*  note: should have a transformSimgaPoints method which given same */
  /*  parameters, because the Pyy calculation depends on alpha and beta. */
  /*  compute sigma points */
  /*  collect parameters */
  /*  compute unscaled sigma points */
  jj = mx->size[0];
  i14 = X->size[0] * X->size[1];
  X->size[0] = jj;
  emxEnsureCapacity((emxArray__common *)X, i14, (int)sizeof(double));
  jj = (int)(2.0 * (double)mx->size[0] + 1.0);
  i14 = X->size[0] * X->size[1];
  X->size[1] = jj;
  emxEnsureCapacity((emxArray__common *)X, i14, (int)sizeof(double));
  jj = mx->size[0] * (int)(2.0 * (double)mx->size[0] + 1.0);
  for (i14 = 0; i14 < jj; i14++) {
    X->data[i14] = 0.0;
  }

  jj = mx->size[0];
  for (i14 = 0; i14 < jj; i14++) {
    X->data[i14] = mx->data[i14];
  }

  emxInit_real_T(&y, 2);
  ajj = (double)mx->size[0] + parameter;
  i14 = y->size[0] * y->size[1];
  y->size[0] = Pxx->size[0];
  y->size[1] = Pxx->size[1];
  emxEnsureCapacity((emxArray__common *)y, i14, (int)sizeof(double));
  jj = Pxx->size[0] * Pxx->size[1];
  for (i14 = 0; i14 < jj; i14++) {
    y->data[i14] = ajj * Pxx->data[i14];
  }

  n = y->size[1];
  if (y->size[1] == 0) {
  } else {
    b_n = y->size[0];
    info = -1;
    if (y->size[0] == 0) {
    } else {
      colj = 1;
      j = 0;
      exitg1 = false;
      while ((!exitg1) && (j + 1 <= b_n)) {
        jj = (colj + j) - 1;
        ajj = 0.0;
        if (j < 1) {
        } else {
          ix = colj;
          iy = colj;
          for (k = 1; k <= j; k++) {
            ajj += y->data[ix - 1] * y->data[iy - 1];
            ix++;
            iy++;
          }
        }

        ajj = y->data[jj] - ajj;
        if (ajj > 0.0) {
          ajj = sqrt(ajj);
          y->data[jj] = ajj;
          if (j + 1 < b_n) {
            nmj = (b_n - j) - 2;
            jjp1 = jj + b_n;
            coljp1 = colj + b_n;
            if ((j == 0) || (nmj + 1 == 0)) {
            } else {
              iy = jjp1;
              i14 = coljp1 + n * nmj;
              for (jj = coljp1; jj <= i14; jj += n) {
                ix = colj;
                c = 0.0;
                i15 = (jj + j) - 1;
                for (k = jj; k <= i15; k++) {
                  c += y->data[k - 1] * y->data[ix - 1];
                  ix++;
                }

                y->data[iy] += -c;
                iy += n;
              }
            }

            ajj = 1.0 / ajj;
            i14 = (jjp1 + b_n * nmj) + 1;
            for (k = jjp1 + 1; k <= i14; k += b_n) {
              y->data[k - 1] *= ajj;
            }

            colj = coljp1;
          }

          j++;
        } else {
          y->data[jj] = ajj;
          info = j;
          exitg1 = true;
        }
      }
    }

    if (info + 1 == 0) {
      jj = n;
    } else {
      jj = info;
    }

    for (j = 0; j + 1 <= jj; j++) {
      for (k = j + 1; k + 1 <= jj; k++) {
        y->data[k + y->size[0] * j] = 0.0;
      }
    }
  }

  emxInit_real_T(&matrixSq, 2);
  i14 = matrixSq->size[0] * matrixSq->size[1];
  matrixSq->size[0] = y->size[1];
  matrixSq->size[1] = y->size[0];
  emxEnsureCapacity((emxArray__common *)matrixSq, i14, (int)sizeof(double));
  jj = y->size[0];
  for (i14 = 0; i14 < jj; i14++) {
    k = y->size[1];
    for (i15 = 0; i15 < k; i15++) {
      matrixSq->data[i15 + matrixSq->size[0] * i14] = y->data[i14 + y->size[0] *
        i15];
    }
  }

  emxInit_real_T(&r790, 2);
  c_repmat(mx, mx->size[0], r790);
  if (2U > mx->size[0] + 1U) {
    i14 = 0;
  } else {
    i14 = 1;
  }

  jj = r790->size[1];
  for (i15 = 0; i15 < jj; i15++) {
    k = r790->size[0];
    for (jjp1 = 0; jjp1 < k; jjp1++) {
      X->data[jjp1 + X->size[0] * (i14 + i15)] = r790->data[jjp1 + r790->size[0]
        * i15] + matrixSq->data[jjp1 + matrixSq->size[0] * i15];
    }
  }

  c_repmat(mx, mx->size[0], r790);
  u0 = ((unsigned int)mx->size[0] << 1) + 1U;
  if (mx->size[0] + 2U > u0) {
    i14 = 0;
  } else {
    i14 = mx->size[0] + 1;
  }

  jj = r790->size[1];
  for (i15 = 0; i15 < jj; i15++) {
    k = r790->size[0];
    for (jjp1 = 0; jjp1 < k; jjp1++) {
      X->data[jjp1 + X->size[0] * (i14 + i15)] = r790->data[jjp1 + r790->size[0]
        * i15] - matrixSq->data[jjp1 + matrixSq->size[0] * i15];
    }
  }

  emxFree_real_T(&matrixSq);

  /*  compute weights */
  i14 = W->size[0] * W->size[1];
  W->size[0] = 1;
  emxEnsureCapacity((emxArray__common *)W, i14, (int)sizeof(double));
  jj = (int)(2.0 * (double)mx->size[0] + 1.0);
  i14 = W->size[0] * W->size[1];
  W->size[1] = jj;
  emxEnsureCapacity((emxArray__common *)W, i14, (int)sizeof(double));
  jj = (int)(2.0 * (double)mx->size[0] + 1.0);
  for (i14 = 0; i14 < jj; i14++) {
    W->data[i14] = 0.0;
  }

  W->data[0] = parameter / ((double)mx->size[0] + parameter);
  u0 = ((unsigned int)mx->size[0] << 1) + 1U;
  if (2U > u0) {
    i14 = 0;
    i15 = 0;
  } else {
    i14 = 1;
    i15 = (int)u0;
  }

  emxInit_int32_T(&r791, 2);
  jjp1 = r791->size[0] * r791->size[1];
  r791->size[0] = 1;
  r791->size[1] = i15 - i14;
  emxEnsureCapacity((emxArray__common *)r791, jjp1, (int)sizeof(int));
  jj = i15 - i14;
  for (i15 = 0; i15 < jj; i15++) {
    r791->data[r791->size[0] * i15] = i14 + i15;
  }

  ajj = 0.5 / ((double)mx->size[0] + parameter);
  jj = r791->size[0] * r791->size[1];
  for (i14 = 0; i14 < jj; i14++) {
    W->data[r791->data[i14]] = ajj;
  }

  emxFree_int32_T(&r791);
  b_emxInit_real_T(&b_X, 1);

  /*  scale the sigma points */
  jj = X->size[0];
  i14 = b_X->size[0];
  b_X->size[0] = jj;
  emxEnsureCapacity((emxArray__common *)b_X, i14, (int)sizeof(double));
  for (i14 = 0; i14 < jj; i14++) {
    b_X->data[i14] = X->data[i14];
  }

  b_emxInit_real_T(&c_X, 1);
  c_repmat(b_X, X->size[1], r790);
  jj = X->size[0];
  i14 = c_X->size[0];
  c_X->size[0] = jj;
  emxEnsureCapacity((emxArray__common *)c_X, i14, (int)sizeof(double));
  emxFree_real_T(&b_X);
  for (i14 = 0; i14 < jj; i14++) {
    c_X->data[i14] = X->data[i14];
  }

  c_repmat(c_X, X->size[1], y);
  i14 = X->size[0] * X->size[1];
  X->size[0] = y->size[0];
  X->size[1] = y->size[1];
  emxEnsureCapacity((emxArray__common *)X, i14, (int)sizeof(double));
  jj = y->size[0] * y->size[1];
  emxFree_real_T(&c_X);
  for (i14 = 0; i14 < jj; i14++) {
    X->data[i14] = y->data[i14] + (X->data[i14] - r790->data[i14]);
  }

  emxFree_real_T(&y);
  emxFree_real_T(&r790);

  /*  compute weights */
  if (2 > W->size[1]) {
    i14 = 0;
    i15 = 0;
  } else {
    i14 = 1;
    i15 = W->size[1];
  }

  if (2 > W->size[1]) {
    jjp1 = 0;
  } else {
    jjp1 = 1;
  }

  emxInit_real_T(&b_W, 2);
  jj = b_W->size[0] * b_W->size[1];
  b_W->size[0] = 1;
  b_W->size[1] = i15 - i14;
  emxEnsureCapacity((emxArray__common *)b_W, jj, (int)sizeof(double));
  jj = i15 - i14;
  for (i15 = 0; i15 < jj; i15++) {
    b_W->data[b_W->size[0] * i15] = W->data[i14 + i15];
  }

  emxInit_real_T(&r792, 2);
  rdivide(b_W, 1.0, r792);
  jj = r792->size[1];
  emxFree_real_T(&b_W);
  for (i14 = 0; i14 < jj; i14++) {
    W->data[jjp1 + i14] = r792->data[r792->size[0] * i14];
  }

  emxFree_real_T(&r792);
}

/*
 * File trailer for computeSigmaPoints.c
 *
 * [EOF]
 */
