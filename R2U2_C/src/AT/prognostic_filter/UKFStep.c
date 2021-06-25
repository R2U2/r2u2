/*
 * File: UKFStep.c
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
#include "colon.h"
#include "wcov.h"
#include "wmean.h"
#include "StateEqnUKF.h"
#include "computeSigmaPoints.h"
#include <stdio.h>

/* Function Declarations */
static double b_eml_xnrm2(int n, const double x_data[], int ix0);
static void eml_lusolve(const double A_data[], const int A_size[2],
  emxArray_real_T *B);
static void eml_matlab_zlarf(int m, int n, int iv0, double tau, double C_data[],
  double work_data[]);
static void eml_qrsolve(const double A_data[], const int A_size[2],
  emxArray_real_T *B, emxArray_real_T *Y);
static double eml_xnrm2(int n, const double x_data[], int ix0);
static double rt_hypotd_snf(double u0, double u1);

/* Function Definitions */

/*
 * Arguments    : int n
 *                const double x_data[]
 *                int ix0
 * Return Type  : double
 */
static double b_eml_xnrm2(int n, const double x_data[], int ix0)
{
  double y;
  double scale;
  int k;
  double absxk;
  double t;
  y = 0.0;
  if (n < 1) {
  } else if (n == 1) {
    y = fabs(x_data[ix0 - 1]);
  } else {
    scale = 2.2250738585072014E-308;
    for (k = ix0; k <= ix0 + 1; k++) {
      absxk = fabs(x_data[k - 1]);
      if (absxk > scale) {
        t = scale / absxk;
        y = 1.0 + y * t * t;
        scale = absxk;
      } else {
        t = absxk / scale;
        y += t * t;
      }
    }

    y = scale * sqrt(y);
  }

  return y;
}

/*
 * Arguments    : const double A_data[]
 *                const int A_size[2]
 *                emxArray_real_T *B
 * Return Type  : void
 */
static void eml_lusolve(const double A_data[], const int A_size[2],
  emxArray_real_T *B)
{
  int ix;
  int iy;
  double b_A_data[4];
  int tmp_size[2];
  int tmp_data[2];
  int ipiv_data[2];
  int k;
  double temp;
  int nb;
  int jBcol;
  int jAcol;
  ix = A_size[0] * A_size[1];
  for (iy = 0; iy < ix; iy++) {
    b_A_data[iy] = A_data[iy];
  }

  eml_signed_integer_colon(2, tmp_data, tmp_size);
  ix = tmp_size[0] * tmp_size[1];
  for (iy = 0; iy < ix; iy++) {
    ipiv_data[iy] = tmp_data[iy];
  }

  ix = 0;
  if (fabs(b_A_data[1]) > fabs(b_A_data[0])) {
    ix = 1;
  }

  if (b_A_data[ix] != 0.0) {
    if (ix != 0) {
      ipiv_data[0] = 2;
      ix = 0;
      iy = 1;
      for (k = 0; k < 2; k++) {
        temp = b_A_data[ix];
        b_A_data[ix] = b_A_data[iy];
        b_A_data[iy] = temp;
        ix += 2;
        iy += 2;
      }
    }

    b_A_data[1] /= b_A_data[0];
  }

  if (b_A_data[2] != 0.0) {
    b_A_data[3] += b_A_data[1] * -b_A_data[2];
  }

  nb = B->size[0];
  if (B->size[0] == 0) {
  } else {
    for (iy = 0; iy < 2; iy++) {
      jBcol = nb * iy;
      jAcol = iy << 1;
      k = 1;
      while (k <= iy) {
        if (b_A_data[jAcol] != 0.0) {
          for (ix = 0; ix + 1 <= nb; ix++) {
            B->data[ix + jBcol] -= b_A_data[jAcol] * B->data[ix];
          }
        }

        k = 2;
      }

      temp = 1.0 / b_A_data[iy + jAcol];
      for (ix = 0; ix + 1 <= nb; ix++) {
        B->data[ix + jBcol] *= temp;
      }
    }
  }

  if (B->size[0] == 0) {
  } else {
    for (iy = 1; iy > -1; iy += -1) {
      jBcol = nb * iy;
      jAcol = (iy << 1) + 1;
      k = iy + 2;
      while (k <= 2) {
        if (b_A_data[jAcol] != 0.0) {
          for (ix = 0; ix + 1 <= nb; ix++) {
            B->data[ix + jBcol] -= b_A_data[jAcol] * B->data[ix + nb];
          }
        }

        k = 3;
      }
    }
  }

  if (ipiv_data[0] != 1) {
    ix = ipiv_data[0] - 1;
    for (iy = 0; iy + 1 <= nb; iy++) {
      temp = B->data[iy];
      B->data[iy] = B->data[iy + B->size[0] * ix];
      B->data[iy + B->size[0] * ix] = temp;
    }
  }
}

/*
 * Arguments    : int m
 *                int n
 *                int iv0
 *                double tau
 *                double C_data[]
 *                double work_data[]
 * Return Type  : void
 */
static void eml_matlab_zlarf(int m, int n, int iv0, double tau, double C_data[],
  double work_data[])
{
  int lastv;
  int i;
  int lastc;
  boolean_T exitg2;
  int32_T exitg1;
  int jA;
  int jy;
  int iac;
  int ix;
  double c;
  int i32;
  if (tau != 0.0) {
    lastv = m;
    i = iv0 + m;
    while ((lastv > 0) && (C_data[i - 2] == 0.0)) {
      lastv--;
      i--;
    }

    lastc = n;
    exitg2 = false;
    while ((!exitg2) && (lastc > 0)) {
      i = 3;
      do {
        exitg1 = 0;
        if (i <= lastv + 2) {
          if (C_data[i - 1] != 0.0) {
            exitg1 = 1;
          } else {
            i++;
          }
        } else {
          lastc = 0;
          exitg1 = 2;
        }
      } while (exitg1 == 0);

      if (exitg1 == 1) {
        exitg2 = true;
      }
    }
  } else {
    lastv = 0;
    lastc = 0;
  }

  if (lastv > 0) {
    if (lastc == 0) {
    } else {
      jA = 1;
      while (jA <= lastc) {
        work_data[0] = 0.0;
        jA = 2;
      }

      jA = 0;
      jy = (lastc - 1) << 1;
      for (iac = 3; iac <= jy + 3; iac += 2) {
        ix = iv0;
        c = 0.0;
        i32 = (iac + lastv) - 1;
        for (i = iac; i <= i32; i++) {
          c += C_data[i - 1] * C_data[ix - 1];
          ix++;
        }

        work_data[jA] += c;
        jA++;
      }
    }

    if (-tau == 0.0) {
    } else {
      jA = 2;
      jy = 0;
      i = 1;
      while (i <= lastc) {
        if (work_data[jy] != 0.0) {
          c = work_data[jy] * -tau;
          ix = iv0;
          i32 = lastv + jA;
          for (i = jA; i + 1 <= i32; i++) {
            C_data[i] += C_data[ix - 1] * c;
            ix++;
          }
        }

        jy++;
        jA += 2;
        i = 2;
      }
    }
  }
}

/*
 * Arguments    : const double A_data[]
 *                const int A_size[2]
 *                emxArray_real_T *B
 *                emxArray_real_T *Y
 * Return Type  : void
 */
static void eml_qrsolve(const double A_data[], const int A_size[2],
  emxArray_real_T *B, emxArray_real_T *Y)
{
  int nb;
  int mn;
  int ix;
  int iy;
  double b_A_data[4];
  int n;
  int b_mn;
  double tau_data[2];
  int jpvt_size[2];
  int jpvt_data[2];
  double work_data[2];
  double vn1_data[2];
  double vn2_data[2];
  int k;
  double tol;
  double rankR;
  double absxk;
  double t;
  int i;
  int i_i;
  int nmi;
  int pvt;
  unsigned int unnamed_idx_1;
  nb = B->size[1] - 1;
  if (2 <= A_size[1]) {
    mn = 1;
  } else {
    mn = A_size[1] - 1;
  }

  ix = A_size[0] * A_size[1];
  for (iy = 0; iy < ix; iy++) {
    b_A_data[iy] = A_data[iy];
  }

  n = A_size[1];
  if (2 <= A_size[1]) {
    b_mn = 2;
  } else {
    b_mn = A_size[1];
  }

  eml_signed_integer_colon(A_size[1], jpvt_data, jpvt_size);
  ix = (signed char)A_size[1];
  for (iy = 0; iy < ix; iy++) {
    work_data[iy] = 0.0;
  }

  k = 1;
  for (iy = 0; iy + 1 <= n; iy++) {
    tol = 0.0;
    rankR = 2.2250738585072014E-308;
    for (ix = k; ix <= k + 1; ix++) {
      absxk = fabs(A_data[ix - 1]);
      if (absxk > rankR) {
        t = rankR / absxk;
        tol = 1.0 + tol * t * t;
        rankR = absxk;
      } else {
        t = absxk / rankR;
        tol += t * t;
      }
    }

    tol = rankR * sqrt(tol);
    vn1_data[iy] = tol;
    vn2_data[iy] = vn1_data[iy];
    k += 2;
  }

  for (i = 0; i + 1 <= b_mn; i++) {
    i_i = i + (i << 1);
    nmi = n - i;
    if (nmi < 1) {
      ix = -1;
    } else {
      ix = 0;
      if ((nmi > 1) && (fabs(vn1_data[1]) > fabs(vn1_data[i]))) {
        ix = 1;
      }
    }

    pvt = i + ix;
    if (pvt + 1 != i + 1) {
      ix = pvt << 1;
      iy = i << 1;
      for (k = 0; k < 2; k++) {
        tol = b_A_data[ix];
        b_A_data[ix] = b_A_data[iy];
        b_A_data[iy] = tol;
        ix++;
        iy++;
      }

      ix = jpvt_data[pvt];
      jpvt_data[pvt] = jpvt_data[i];
      jpvt_data[i] = ix;
      vn1_data[pvt] = vn1_data[i];
      vn2_data[pvt] = vn2_data[i];
    }

    if (i + 1 < 2) {
      rankR = b_A_data[i_i];
      absxk = 0.0;
      tol = eml_xnrm2(1, b_A_data, i_i + 2);
      if (tol != 0.0) {
        tol = rt_hypotd_snf(b_A_data[i_i], tol);
        if (b_A_data[i_i] >= 0.0) {
          tol = -tol;
        }

        if (fabs(tol) < 1.0020841800044864E-292) {
          iy = 0;
          do {
            iy++;
            for (k = i_i + 1; k + 1 <= i_i + 2; k++) {
              b_A_data[k] *= 9.9792015476736E+291;
            }

            tol *= 9.9792015476736E+291;
            rankR *= 9.9792015476736E+291;
          } while (!(fabs(tol) >= 1.0020841800044864E-292));

          tol = eml_xnrm2(1, b_A_data, i_i + 2);
          tol = rt_hypotd_snf(rankR, tol);
          if (rankR >= 0.0) {
            tol = -tol;
          }

          absxk = (tol - rankR) / tol;
          rankR = 1.0 / (rankR - tol);
          for (k = i_i + 1; k + 1 <= i_i + 2; k++) {
            b_A_data[k] *= rankR;
          }

          for (k = 1; k <= iy; k++) {
            tol *= 1.0020841800044864E-292;
          }

          rankR = tol;
        } else {
          absxk = (tol - b_A_data[i_i]) / tol;
          rankR = 1.0 / (b_A_data[i_i] - tol);
          for (k = i_i + 1; k + 1 <= i_i + 2; k++) {
            b_A_data[k] *= rankR;
          }

          rankR = tol;
        }
      }

      tau_data[0] = absxk;
    } else {
      rankR = b_A_data[i_i];
      tau_data[1] = 0.0;
    }

    b_A_data[i_i] = rankR;
    if (i + 1 < n) {
      rankR = b_A_data[i_i];
      b_A_data[i_i] = 1.0;
      eml_matlab_zlarf(2, nmi - 1, i_i + 1, tau_data[0], b_A_data, work_data);
      b_A_data[i_i] = rankR;
    }

    iy = i + 2;
    while (iy <= n) {
      if (vn1_data[1] != 0.0) {
        tol = fabs(b_A_data[i + 2]) / vn1_data[1];
        tol = 1.0 - tol * tol;
        if (tol < 0.0) {
          tol = 0.0;
        }

        rankR = vn1_data[1] / vn2_data[1];
        rankR = tol * (rankR * rankR);
        if (rankR <= 1.4901161193847656E-8) {
          if (i + 1 < 2) {
            vn1_data[1] = b_eml_xnrm2(1, b_A_data, 4);
            vn2_data[1] = vn1_data[1];
          } else {
            vn1_data[1] = 0.0;
            vn2_data[1] = 0.0;
          }
        } else {
          vn1_data[1] *= sqrt(tol);
        }
      }

      iy = 3;
    }
  }

  rankR = 0.0;
  tol = 2.0 * fabs(b_A_data[0]) * 2.2204460492503131E-16;
  k = 0;
  while ((k <= mn) && (!(fabs(b_A_data[k + (k << 1)]) <= tol))) {
    rankR++;
    k++;
  }

  unnamed_idx_1 = (unsigned int)B->size[1];
  iy = Y->size[0] * Y->size[1];
  Y->size[0] = A_size[1];
  emxEnsureCapacity((emxArray__common *)Y, iy, (int)sizeof(double));
  iy = Y->size[0] * Y->size[1];
  Y->size[1] = (int)unnamed_idx_1;
  emxEnsureCapacity((emxArray__common *)Y, iy, (int)sizeof(double));
  ix = A_size[1] * (int)unnamed_idx_1;
  for (iy = 0; iy < ix; iy++) {
    Y->data[iy] = 0.0;
  }

  for (iy = 0; iy <= mn; iy++) {
    if (tau_data[iy] != 0.0) {
      for (k = 0; k <= nb; k++) {
        tol = B->data[iy + B->size[0] * k];
        i = 0;
        while (i <= -iy) {
          tol += b_A_data[1 + (iy << 1)] * B->data[1 + B->size[0] * k];
          i = 1;
        }

        tol *= tau_data[iy];
        if (tol != 0.0) {
          B->data[iy + B->size[0] * k] -= tol;
          i = 0;
          while (i <= -iy) {
            B->data[1 + B->size[0] * k] -= b_A_data[1 + (iy << 1)] * tol;
            i = 1;
          }
        }
      }
    }
  }

  for (k = 0; k <= nb; k++) {
    for (i = 0; i < (int)rankR; i++) {
      Y->data[(jpvt_data[i] + Y->size[0] * k) - 1] = B->data[i + B->size[0] * k];
    }

    for (iy = 0; iy < (int)-(1.0 + (-1.0 - rankR)); iy++) {
      tol = rankR + -(double)iy;
      Y->data[(jpvt_data[(int)tol - 1] + Y->size[0] * k) - 1] /= b_A_data[((int)
        tol + (((int)tol - 1) << 1)) - 1];
      i = 0;
      while (i <= (int)tol - 2) {
        Y->data[(jpvt_data[0] + Y->size[0] * k) - 1] -= Y->data[(jpvt_data[(int)
          tol - 1] + Y->size[0] * k) - 1] * b_A_data[((int)tol - 1) << 1];
        i = 1;
      }
    }
  }
}

/*
 * Arguments    : int n
 *                const double x_data[]
 *                int ix0
 * Return Type  : double
 */
static double eml_xnrm2(int n, const double x_data[], int ix0)
{
  double y;
  double scale;
  int k;
  double absxk;
  double t;
  y = 0.0;
  if (n < 1) {
  } else if (n == 1) {
    y = fabs(x_data[ix0 - 1]);
  } else {
    scale = 2.2250738585072014E-308;
    for (k = ix0; k <= ix0 + 1; k++) {
      absxk = fabs(x_data[k - 1]);
      if (absxk > scale) {
        t = scale / absxk;
        y = 1.0 + y * t * t;
        scale = absxk;
      } else {
        t = absxk / scale;
        y += t * t;
      }
    }

    y = scale * sqrt(y);
  }

  return y;
}

/*
 * Arguments    : double u0
 *                double u1
 * Return Type  : double
 */
static double rt_hypotd_snf(double u0, double u1)
{
  double y;
  double a;
  double b;
  a = fabs(u0);
  b = fabs(u1);
  if (a < b) {
    a /= b;
    y = b * sqrt(a * a + 1.0);
  } else if (a > b) {
    b /= a;
    y = a * sqrt(b * b + 1.0);
  } else if (rtIsNaN(b)) {
    y = b;
  } else {
    y = a * 1.4142135623730951;
  }

  return y;
}

/*
 * Arguments    : double t
 *                double newT
 *                const emxArray_real_T *xOld
 *                const emxArray_real_T *POld
 *                const emxArray_real_T *uOld
 *                const emxArray_real_T *u
 *                const emxArray_real_T *z
 *                const emxArray_real_T *modelVariance
 *                const emxArray_real_T *sensorVariance
 *                emxArray_real_T *x
 *                emxArray_real_T *P
 *                emxArray_real_T *zhat
 * Return Type  : void
 */
void UKFStep(double t, double newT, const emxArray_real_T *xOld, const
             emxArray_real_T *POld, const emxArray_real_T *uOld, const
             emxArray_real_T *u, const emxArray_real_T *z, const emxArray_real_T
             *modelVariance, const emxArray_real_T *sensorVariance,
             emxArray_real_T *x, emxArray_real_T *P, emxArray_real_T *zhat)
{
  emxArray_real_T *Q;
  int unnamed_idx_0;
  int br;
  int i20;
  int loop_ub;
  emxArray_real_T *R;
  emxArray_real_T *Xkk1;
  emxArray_real_T *Zkk1;
  emxArray_real_T *X;
  emxArray_real_T *W;
  int zkk1_size[1];
  double zkk1_data[2];
  int Pzz_size[2];
  double Pzz_data[4];
  double b_W;
  emxArray_real_T *Pxz;
  emxArray_real_T *c_W;
  double b_Zkk1[2];
  int i21;
  emxArray_real_T *d_W;
  emxArray_real_T *b_Pxz;
  double b_Pzz_data[4];
  double c_Pzz_data[4];
  int b_Pzz_size[2];
  emxArray_real_T *c_Pxz;
  emxArray_real_T *r795;
  emxArray_real_T *b;
  emxArray_real_T *C;
  int k;
  int m;
  int ic;
  int ar;
  int ia;
  int c;
  (void)u;
  emxInit_real_T(&Q, 2);
  unnamed_idx_0 = modelVariance->size[1];
  br = modelVariance->size[1];
  i20 = Q->size[0] * Q->size[1];
  Q->size[0] = unnamed_idx_0;
  emxEnsureCapacity((emxArray__common *)Q, i20, (int)sizeof(double));
  i20 = Q->size[0] * Q->size[1];
  Q->size[1] = br;
  emxEnsureCapacity((emxArray__common *)Q, i20, (int)sizeof(double));
  loop_ub = unnamed_idx_0 * br;
  for (i20 = 0; i20 < loop_ub; i20++) {
    Q->data[i20] = 0.0;
  }

  for (unnamed_idx_0 = 0; unnamed_idx_0 + 1 <= modelVariance->size[1];
       unnamed_idx_0++) {
    Q->data[unnamed_idx_0 + Q->size[0] * unnamed_idx_0] = modelVariance->
      data[unnamed_idx_0];
  }

  emxInit_real_T(&R, 2);
  unnamed_idx_0 = sensorVariance->size[1];
  br = sensorVariance->size[1];
  i20 = R->size[0] * R->size[1];
  R->size[0] = unnamed_idx_0;
  emxEnsureCapacity((emxArray__common *)R, i20, (int)sizeof(double));
  i20 = R->size[0] * R->size[1];
  R->size[1] = br;
  emxEnsureCapacity((emxArray__common *)R, i20, (int)sizeof(double));
  loop_ub = unnamed_idx_0 * br;
  for (i20 = 0; i20 < loop_ub; i20++) {
    R->data[i20] = 0.0;
  }

  for (unnamed_idx_0 = 0; unnamed_idx_0 + 1 <= sensorVariance->size[1];
       unnamed_idx_0++) {
    R->data[unnamed_idx_0 + R->size[0] * unnamed_idx_0] = sensorVariance->
      data[unnamed_idx_0];
  }

  emxInit_real_T(&Xkk1, 2);
  emxInit_real_T(&Zkk1, 2);
  emxInit_real_T(&X, 2);
  emxInit_real_T(&W, 2);

  /*  initialize sizes */
  /*  1. Predict */
  /*  compute sigma points */
  b_computeSigmaPoints(xOld, POld, X, W);

  /*  propagate sigma points through transition function */
  StateEqnUKF(X, uOld, newT - t, Xkk1);

  /*  recombine weighted sigma points to produce predicted state */
  /*  and covariance */
  wmean(Xkk1, W, x);
  wcov(Xkk1, W, P);

  /*  propagate sigma points through observation function */
  b_OutputEqnUKF(Xkk1, Zkk1);

  /*  recombine weighted sigma points to produce predicted */
  /*  measurement and covariance */
  c_wmean(Zkk1, W, zkk1_data, zkk1_size);
  b_wcov(Zkk1, W, Pzz_data, Pzz_size);
  loop_ub = Pzz_size[0] * Pzz_size[1];
  for (i20 = 0; i20 < loop_ub; i20++) {
    b_W = Pzz_data[i20] + R->data[i20];
    Pzz_data[i20] = b_W;
  }

  emxInit_real_T(&Pxz, 2);

  /*  2. Update */
  /*  compute state-measurement cross-covariance matrix */
  unnamed_idx_0 = x->size[0];
  i20 = Pxz->size[0] * Pxz->size[1];
  Pxz->size[0] = unnamed_idx_0;
  emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
  i20 = Pxz->size[0] * Pxz->size[1];
  Pxz->size[1] = zkk1_size[0];
  emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
  loop_ub = x->size[0] * zkk1_size[0];
  for (i20 = 0; i20 < loop_ub; i20++) {
    Pxz->data[i20] = 0.0;
  }

  unnamed_idx_0 = 0;
  b_emxInit_real_T(&c_W, 1);
  while (unnamed_idx_0 <= W->size[1] - 1) {
    b_W = W->data[unnamed_idx_0];
    loop_ub = Xkk1->size[0];
    i20 = c_W->size[0];
    c_W->size[0] = loop_ub;
    emxEnsureCapacity((emxArray__common *)c_W, i20, (int)sizeof(double));
    for (i20 = 0; i20 < loop_ub; i20++) {
      c_W->data[i20] = b_W * (Xkk1->data[i20 + Xkk1->size[0] * unnamed_idx_0] -
        x->data[i20]);
    }

    for (i20 = 0; i20 < 2; i20++) {
      b_Zkk1[i20] = Zkk1->data[i20 + Zkk1->size[0] * unnamed_idx_0] -
        zkk1_data[i20];
    }

    i20 = Pxz->size[0] * Pxz->size[1];
    Pxz->size[0] = c_W->size[0];
    Pxz->size[1] = 2;
    emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
    loop_ub = c_W->size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      for (i21 = 0; i21 < 2; i21++) {
        b_W = c_W->data[i20] * b_Zkk1[i21];
        Pxz->data[i20 + Pxz->size[0] * i21] += b_W;
      }
    }

    unnamed_idx_0++;
  }

  emxFree_real_T(&c_W);
  b_emxInit_real_T(&d_W, 1);
  b_W = (W->data[0] + 1.0) - 1.0;
  loop_ub = Xkk1->size[0];
  i20 = d_W->size[0];
  d_W->size[0] = loop_ub;
  emxEnsureCapacity((emxArray__common *)d_W, i20, (int)sizeof(double));
  emxFree_real_T(&W);
  for (i20 = 0; i20 < loop_ub; i20++) {
    d_W->data[i20] = b_W * (Xkk1->data[i20] - x->data[i20]);
  }

  for (i20 = 0; i20 < 2; i20++) {
    b_Zkk1[i20] = Zkk1->data[i20] - zkk1_data[i20];
  }

  emxFree_real_T(&Zkk1);
  emxInit_real_T(&b_Pxz, 2);
  i20 = b_Pxz->size[0] * b_Pxz->size[1];
  b_Pxz->size[0] = d_W->size[0];
  b_Pxz->size[1] = 2;
  emxEnsureCapacity((emxArray__common *)b_Pxz, i20, (int)sizeof(double));
  loop_ub = d_W->size[0];
  for (i20 = 0; i20 < loop_ub; i20++) {
    for (i21 = 0; i21 < 2; i21++) {
      b_W = d_W->data[i20] * b_Zkk1[i21];
      b_Pxz->data[i20 + b_Pxz->size[0] * i21] = Pxz->data[i20 + Pxz->size[0] *
        i21] + b_W;
    }
  }

  emxFree_real_T(&d_W);

  /*  compute kalman gain */
  if (b_Pxz->size[0] == 0) {
    i20 = Pxz->size[0] * Pxz->size[1];
    Pxz->size[0] = 0;
    emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
    i20 = Pxz->size[0] * Pxz->size[1];
    Pxz->size[1] = Pzz_size[0];
    emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
  } else if (Pzz_size[0] == 2) {
    eml_lusolve(Pzz_data, Pzz_size, b_Pxz);
    i20 = Pxz->size[0] * Pxz->size[1];
    Pxz->size[0] = b_Pxz->size[0];
    Pxz->size[1] = 2;
    emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
    loop_ub = b_Pxz->size[0] * b_Pxz->size[1];
    for (i20 = 0; i20 < loop_ub; i20++) {
      Pxz->data[i20] = b_Pxz->data[i20];
    }
  } else {
    loop_ub = Pzz_size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      unnamed_idx_0 = Pzz_size[1];
      for (i21 = 0; i21 < unnamed_idx_0; i21++) {
        c_Pzz_data[i21 + Pzz_size[1] * i20] = Pzz_data[i20 + Pzz_size[0] * i21];
      }
    }

    b_Pzz_size[0] = 2;
    b_Pzz_size[1] = Pzz_size[0];
    loop_ub = Pzz_size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      for (i21 = 0; i21 < 2; i21++) {
        b_Pzz_data[i21 + (i20 << 1)] = c_Pzz_data[i21 + Pzz_size[1] * i20];
      }
    }

    emxInit_real_T(&c_Pxz, 2);
    i20 = c_Pxz->size[0] * c_Pxz->size[1];
    c_Pxz->size[0] = 2;
    c_Pxz->size[1] = b_Pxz->size[0];
    emxEnsureCapacity((emxArray__common *)c_Pxz, i20, (int)sizeof(double));
    loop_ub = b_Pxz->size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      for (i21 = 0; i21 < 2; i21++) {
        c_Pxz->data[i21 + c_Pxz->size[0] * i20] = b_Pxz->data[i20 + b_Pxz->size
          [0] * i21];
      }
    }

    emxInit_real_T(&r795, 2);
    eml_qrsolve(b_Pzz_data, b_Pzz_size, c_Pxz, r795);
    i20 = Pxz->size[0] * Pxz->size[1];
    Pxz->size[0] = r795->size[1];
    Pxz->size[1] = r795->size[0];
    emxEnsureCapacity((emxArray__common *)Pxz, i20, (int)sizeof(double));
    loop_ub = r795->size[0];
    emxFree_real_T(&c_Pxz);
    for (i20 = 0; i20 < loop_ub; i20++) {
      unnamed_idx_0 = r795->size[1];
      for (i21 = 0; i21 < unnamed_idx_0; i21++) {
        Pxz->data[i21 + Pxz->size[0] * i20] = r795->data[i20 + r795->size[0] *
          i21];
      }
    }

    emxFree_real_T(&r795);
  }

  emxFree_real_T(&b_Pxz);
  b_emxInit_real_T(&b, 1);

  /*  compute state and measurement estimates */
  i20 = b->size[0];
  b->size[0] = z->size[0];
  emxEnsureCapacity((emxArray__common *)b, i20, (int)sizeof(double));
  loop_ub = z->size[0];
  for (i20 = 0; i20 < loop_ub; i20++) {
    b->data[i20] = z->data[i20] - zkk1_data[i20];
  }

  b_emxInit_real_T(&C, 1);
  if ((Pxz->size[1] == 1) || (b->size[0] == 1)) {
    i20 = C->size[0];
    C->size[0] = Pxz->size[0];
    emxEnsureCapacity((emxArray__common *)C, i20, (int)sizeof(double));
    loop_ub = Pxz->size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      C->data[i20] = 0.0;
      unnamed_idx_0 = Pxz->size[1];
      for (i21 = 0; i21 < unnamed_idx_0; i21++) {
        C->data[i20] += Pxz->data[i20 + Pxz->size[0] * i21] * b->data[i21];
      }
    }
  } else {
    k = Pxz->size[1];
    unnamed_idx_0 = Pxz->size[0];
    m = Pxz->size[0];
    i20 = C->size[0];
    C->size[0] = unnamed_idx_0;
    emxEnsureCapacity((emxArray__common *)C, i20, (int)sizeof(double));
    for (i20 = 0; i20 < unnamed_idx_0; i20++) {
      C->data[i20] = 0.0;
    }

    if (Pxz->size[0] == 0) {
    } else {
      unnamed_idx_0 = 0;
      while ((m > 0) && (unnamed_idx_0 <= 0)) {
        for (ic = 1; ic <= m; ic++) {
          C->data[ic - 1] = 0.0;
        }

        unnamed_idx_0 = m;
      }

      br = 0;
      unnamed_idx_0 = 0;
      while ((m > 0) && (unnamed_idx_0 <= 0)) {
        ar = -1;
        i20 = br + k;
        for (loop_ub = br; loop_ub + 1 <= i20; loop_ub++) {
          if (b->data[loop_ub] != 0.0) {
            ia = ar;
            for (ic = 0; ic + 1 <= m; ic++) {
              ia++;
              C->data[ic] += b->data[loop_ub] * Pxz->data[ia];
            }
          }

          ar += m;
        }

        br += k;
        unnamed_idx_0 = m;
      }
    }
  }

  emxFree_real_T(&b);
  i20 = x->size[0];
  emxEnsureCapacity((emxArray__common *)x, i20, (int)sizeof(double));
  loop_ub = x->size[0];
  for (i20 = 0; i20 < loop_ub; i20++) {
    x->data[i20] += C->data[i20];
  }

  emxFree_real_T(&C);
  c_OutputEqnUKF(x, zkk1_data);
  i20 = zhat->size[0];
  zhat->size[0] = 2;
  emxEnsureCapacity((emxArray__common *)zhat, i20, (int)sizeof(double));
  for (i20 = 0; i20 < 2; i20++) {
    zhat->data[i20] = zkk1_data[i20];
  }

  if ((Pxz->size[1] == 1) || (Pzz_size[0] == 1)) {
    i20 = X->size[0] * X->size[1];
    X->size[0] = Pxz->size[0];
    X->size[1] = Pzz_size[1];
    emxEnsureCapacity((emxArray__common *)X, i20, (int)sizeof(double));
    loop_ub = Pxz->size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      unnamed_idx_0 = Pzz_size[1];
      for (i21 = 0; i21 < unnamed_idx_0; i21++) {
        X->data[i20 + X->size[0] * i21] = 0.0;
        br = Pxz->size[1];
        for (ar = 0; ar < br; ar++) {
          X->data[i20 + X->size[0] * i21] += Pxz->data[i20 + Pxz->size[0] * ar] *
            Pzz_data[ar + Pzz_size[0] * i21];
        }
      }
    }
  } else {
    k = Pxz->size[1];
    unnamed_idx_0 = Pxz->size[0];
    m = Pxz->size[0];
    i20 = X->size[0] * X->size[1];
    X->size[0] = unnamed_idx_0;
    emxEnsureCapacity((emxArray__common *)X, i20, (int)sizeof(double));
    i20 = X->size[0] * X->size[1];
    X->size[1] = Pzz_size[1];
    emxEnsureCapacity((emxArray__common *)X, i20, (int)sizeof(double));
    loop_ub = unnamed_idx_0 * Pzz_size[1];
    for (i20 = 0; i20 < loop_ub; i20++) {
      X->data[i20] = 0.0;
    }

    if ((Pxz->size[0] == 0) || (Pzz_size[1] == 0)) {
    } else {
      c = Pxz->size[0] * (Pzz_size[1] - 1);
      unnamed_idx_0 = 0;
      while ((m > 0) && (unnamed_idx_0 <= c)) {
        i20 = unnamed_idx_0 + m;
        for (ic = unnamed_idx_0; ic + 1 <= i20; ic++) {
          X->data[ic] = 0.0;
        }

        unnamed_idx_0 += m;
      }

      br = 0;
      unnamed_idx_0 = 0;
      while ((m > 0) && (unnamed_idx_0 <= c)) {
        ar = -1;
        i20 = br + k;
        for (loop_ub = br; loop_ub + 1 <= i20; loop_ub++) {
          if (Pzz_data[loop_ub] != 0.0) {
            ia = ar;
            i21 = unnamed_idx_0 + m;
            for (ic = unnamed_idx_0; ic + 1 <= i21; ic++) {
              ia++;
              X->data[ic] += Pzz_data[loop_ub] * Pxz->data[ia];
            }
          }

          ar += m;
        }

        br += k;
        unnamed_idx_0 += m;
      }
    }
  }

  i20 = R->size[0] * R->size[1];
  R->size[0] = Pxz->size[1];
  R->size[1] = Pxz->size[0];
  emxEnsureCapacity((emxArray__common *)R, i20, (int)sizeof(double));
  loop_ub = Pxz->size[0];
  for (i20 = 0; i20 < loop_ub; i20++) {
    unnamed_idx_0 = Pxz->size[1];
    for (i21 = 0; i21 < unnamed_idx_0; i21++) {
      R->data[i21 + R->size[0] * i20] = Pxz->data[i20 + Pxz->size[0] * i21];
    }
  }

  emxFree_real_T(&Pxz);
  if ((X->size[1] == 1) || (R->size[0] == 1)) {
    i20 = Xkk1->size[0] * Xkk1->size[1];
    Xkk1->size[0] = X->size[0];
    Xkk1->size[1] = R->size[1];
    emxEnsureCapacity((emxArray__common *)Xkk1, i20, (int)sizeof(double));
    loop_ub = X->size[0];
    for (i20 = 0; i20 < loop_ub; i20++) {
      unnamed_idx_0 = R->size[1];
      for (i21 = 0; i21 < unnamed_idx_0; i21++) {
        Xkk1->data[i20 + Xkk1->size[0] * i21] = 0.0;
        br = X->size[1];
        for (ar = 0; ar < br; ar++) {
          Xkk1->data[i20 + Xkk1->size[0] * i21] += X->data[i20 + X->size[0] * ar]
            * R->data[ar + R->size[0] * i21];
        }
      }
    }
  } else {
    k = X->size[1];
    unnamed_idx_0 = X->size[0];
    br = R->size[1];
    m = X->size[0];
    i20 = Xkk1->size[0] * Xkk1->size[1];
    Xkk1->size[0] = unnamed_idx_0;
    emxEnsureCapacity((emxArray__common *)Xkk1, i20, (int)sizeof(double));
    i20 = Xkk1->size[0] * Xkk1->size[1];
    Xkk1->size[1] = br;
    emxEnsureCapacity((emxArray__common *)Xkk1, i20, (int)sizeof(double));
    loop_ub = unnamed_idx_0 * br;
    for (i20 = 0; i20 < loop_ub; i20++) {
      Xkk1->data[i20] = 0.0;
    }

    if ((X->size[0] == 0) || (R->size[1] == 0)) {
    } else {
      c = X->size[0] * (R->size[1] - 1);
      unnamed_idx_0 = 0;
      while ((m > 0) && (unnamed_idx_0 <= c)) {
        i20 = unnamed_idx_0 + m;
        for (ic = unnamed_idx_0; ic + 1 <= i20; ic++) {
          Xkk1->data[ic] = 0.0;
        }

        unnamed_idx_0 += m;
      }

      br = 0;
      unnamed_idx_0 = 0;
      while ((m > 0) && (unnamed_idx_0 <= c)) {
        ar = -1;
        i20 = br + k;
        for (loop_ub = br; loop_ub + 1 <= i20; loop_ub++) {
          if (R->data[loop_ub] != 0.0) {
            ia = ar;
            i21 = unnamed_idx_0 + m;
            for (ic = unnamed_idx_0; ic + 1 <= i21; ic++) {
              ia++;
              Xkk1->data[ic] += R->data[loop_ub] * X->data[ia];
            }
          }

          ar += m;
        }

        br += k;
        unnamed_idx_0 += m;
      }
    }
  }

  emxFree_real_T(&X);
  emxFree_real_T(&R);
  i20 = P->size[0] * P->size[1];
  emxEnsureCapacity((emxArray__common *)P, i20, (int)sizeof(double));
  unnamed_idx_0 = P->size[0];
  br = P->size[1];
  loop_ub = unnamed_idx_0 * br;
  for (i20 = 0; i20 < loop_ub; i20++) {
    P->data[i20] = (P->data[i20] + Q->data[i20]) - Xkk1->data[i20];
  }

  emxFree_real_T(&Xkk1);
  emxFree_real_T(&Q);

  /*  compute sigma points */
  /*  [X,W] = Observers.computeSigmaPoints(x,P,'symmetric',[-5 0],1); */
  /*  sigmaPoints = struct('x',X,'w',W,'z',Battery.OutputEqnUKF(newT,X,u,0)); */
}

/*
 * File trailer for UKFStep.c
 *
 * [EOF]
 */
