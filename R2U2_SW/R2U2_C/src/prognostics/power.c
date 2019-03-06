/*
 * File: power.c
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
#include "power.h"
#include "BHM_emxutil.h"
#include "BHM_rtwutil.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void b_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv2[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv2[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv2[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv2[1]; k++) {
    y->data[k] = a->data[k] * a->data[k];
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void c_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv3[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv3[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv3[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv3[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 3.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void d_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv4[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv4[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv4[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv4[1]; k++) {
    y->data[k] = 1.0 / a->data[k];
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void e_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv5[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv5[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv5[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv5[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 4.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void f_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv6[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv6[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv6[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv6[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -2.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void g_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv7[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv7[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv7[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv7[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 5.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void h_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv8[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv8[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv8[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv8[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -3.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void i_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv9[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv9[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv9[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv9[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 6.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void j_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv10[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv10[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv10[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv10[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -4.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void k_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv11[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv11[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv11[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv11[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 7.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void l_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv12[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv12[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv12[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv12[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -5.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void m_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv13[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv13[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv13[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv13[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 8.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void n_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv14[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv14[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv14[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv14[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -6.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void o_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv15[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv15[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv15[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv15[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 9.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void p_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv16[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv16[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv16[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv16[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -7.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv1[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv1[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv1[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv1[1]; k++) {
    y->data[k] = a->data[k];
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void q_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv17[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv17[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv17[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv17[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 10.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void r_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv18[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv18[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv18[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv18[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -8.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void s_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv19[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv19[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv19[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv19[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 11.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void t_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv20[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv20[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv20[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv20[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -9.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void u_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv21[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv21[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv21[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv21[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 12.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void v_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv22[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv22[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv22[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv22[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -10.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void w_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv23[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv23[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv23[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv23[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], 13.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void x_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv24[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv24[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv24[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv24[1]; k++) {
    y->data[k] = rt_powd_snf(a->data[k], -11.0);
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                emxArray_real_T *y
 * Return Type  : void
 */
void y_power(const emxArray_real_T *a, emxArray_real_T *y)
{
  unsigned int uv26[2];
  int k;
  for (k = 0; k < 2; k++) {
    uv26[k] = (unsigned int)a->size[k];
  }

  k = y->size[0] * y->size[1];
  y->size[0] = 1;
  y->size[1] = (int)uv26[1];
  emxEnsureCapacity((emxArray__common *)y, k, (int)sizeof(double));
  for (k = 0; k < (int)uv26[1]; k++) {
    y->data[k] = sqrt(a->data[k]);
  }
}

/*
 * File trailer for power.c
 *
 * [EOF]
 */
