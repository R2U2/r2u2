/*
 * File: CellConstantInputPredict.c
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
#include "fprintf.h"
#include "ThresholdEqnResistance.h"
#include "ThresholdEqnCurrent.h"
#include "ThresholdEqnPower.h"
#include "StateEqnResistance.h"
#include "StateEqnCurrent.h"
#include "StateEqnPower.h"
#include "repmat.h"
#include <stdio.h>

/* Function Declarations */
static double eml_switch_helper(char expr);

/* Function Definitions */

/*
 * Arguments    : char expr
 * Return Type  : double
 */
static double eml_switch_helper(char expr)
{
  double b_index;
  boolean_T b_bool;
  b_bool = false;
  if (expr != 'P') {
  } else {
    b_bool = true;
  }

  if (b_bool) {
    b_index = 0.0;
  } else {
    b_bool = false;
    if (expr != 'I') {
    } else {
      b_bool = true;
    }

    if (b_bool) {
      b_index = 1.0;
    } else {
      b_bool = false;
      if (expr != 'R') {
      } else {
        b_bool = true;
      }

      if (b_bool) {
        b_index = 2.0;
      } else {
        b_index = -1.0;
      }
    }
  }

  return b_index;
}

/*
 * This function does prediction for the following conditions:
 *  1. State is given in weighted samples (eg sigma points). X is nx x N, w
 *  is 1 x N.
 *
 *  2. u is a vector 1 x N, where each sample represents a constant future
 *  input. Samples are equally weighted. Sampling is nested so for each x
 *  sample we simulate all u samples.
 *
 *  3. input says what model to use (constant current, power, or resistance)
 *
 *  4. No future process noise is considered, therefore the only uncertainty
 *  is in the state estimate (X,w) and the inputs (u)
 * Arguments    : double t0
 *                emxArray_real_T *X
 *                const emxArray_real_T *w
 *                const emxArray_real_T *u
 *                char input
 *                double tMax
 *                emxArray_real_T *EOL
 *                emxArray_real_T *RUL
 *                emxArray_real_T *W
 * Return Type  : void
 */
void CellConstantInputPredict(double t0, emxArray_real_T *X, const
  emxArray_real_T *w, const emxArray_real_T *u, char input, double tMax,
  emxArray_real_T *EOL, emxArray_real_T *RUL, emxArray_real_T *W)
{
  emxArray_real_T *b_X;
  int Nu;
  int i0;
  int ixstart;
  emxArray_real_T *U;
  double t;
  double uBlockSize;
  int n;
  emxArray_real_T *b_W;
  double d0;
  int ix;
  double wNu;
  double d1;
  int i1;
  emxArray_boolean_T *B;
  unsigned int uv0[2];
  emxArray_real_T *r0;
  emxArray_real_T *c_X;
  emxArray_real_T *d_X;
  emxArray_real_T *e_X;
  int32_T exitg1;
  boolean_T exitg2;
  emxInit_real_T(&b_X, 2);

// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  /*  load model parameters */
  /*  set up inputs */
  Nu = u->size[1];

// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  /*  reset X,w so have a group for each input sample */
  i0 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = X->size[0];
  b_X->size[1] = X->size[1];
  emxEnsureCapacity((emxArray__common *)b_X, i0, (int)sizeof(double));
  ixstart = X->size[0] * X->size[1];
  for (i0 = 0; i0 < ixstart; i0++) {
    b_X->data[i0] = X->data[i0];
  }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

  emxInit_real_T(&U, 2);
  repmat(b_X, u->size[1], X);
  b_repmat(w, u->size[1], W);
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

  /*  initialize time */
  t = t0;

// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  /*  set up inputs */
  uBlockSize = (double)X->size[1] / (double)u->size[1];
  i0 = U->size[0] * U->size[1];
  U->size[0] = 1;
  emxEnsureCapacity((emxArray__common *)U, i0, (int)sizeof(double));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  ixstart = (int)(uBlockSize * (double)u->size[1]);
  i0 = U->size[0] * U->size[1];
  U->size[1] = ixstart;
  emxEnsureCapacity((emxArray__common *)U, i0, (int)sizeof(double));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  ixstart = (int)(uBlockSize * (double)u->size[1]);
  emxFree_real_T(&b_X);
  for (i0 = 0; i0 < ixstart; i0++) {
    U->data[i0] = 0.0;
  }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

  n = 0;
  emxInit_real_T(&b_W, 2);
  while (n <= Nu - 1) {
    d0 = ((1.0 + (double)n) * uBlockSize - uBlockSize) + 1.0;
    if (d0 > (1.0 + (double)n) * uBlockSize) {
      i0 = 0;
    } else {
      i0 = (int)d0 - 1;
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    ixstart = (int)uBlockSize;
    for (ix = 0; ix < ixstart; ix++) {
      U->data[U->size[0] * (i0 + ix)] = u->data[n];
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    /*  assume inputs equally weighted */
    wNu = 1.0 / (double)Nu;
    d0 = ((1.0 + (double)n) * uBlockSize - uBlockSize) + 1.0;
    d1 = (1.0 + (double)n) * uBlockSize;
    if (d0 > d1) {
      i0 = 0;
      ix = 0;
    } else {
      i0 = (int)d0 - 1;
      ix = (int)d1;
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    d0 = ((1.0 + (double)n) * uBlockSize - uBlockSize) + 1.0;
    if (d0 > (1.0 + (double)n) * uBlockSize) {
      i1 = 0;
    } else {
      i1 = (int)d0 - 1;
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    ixstart = b_W->size[0] * b_W->size[1];
    b_W->size[0] = 1;
    b_W->size[1] = ix - i0;
    emxEnsureCapacity((emxArray__common *)b_W, ixstart, (int)sizeof(double));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
    ixstart = ix - i0;
    for (ix = 0; ix < ixstart; ix++) {
      b_W->data[b_W->size[0] * ix] = W->data[i0 + ix] * wNu;
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    ixstart = b_W->size[1];
    for (i0 = 0; i0 < ixstart; i0++) {
      W->data[i1 + i0] = b_W->data[b_W->size[0] * i0];
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    n++;
  }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

  emxFree_real_T(&b_W);
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

  /*  initialize EOL & RUL */
  i0 = EOL->size[0] * EOL->size[1];
  EOL->size[0] = 1;
  emxEnsureCapacity((emxArray__common *)EOL, i0, (int)sizeof(double));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  ixstart = X->size[1];
  i0 = EOL->size[0] * EOL->size[1];
  EOL->size[1] = ixstart;
  emxEnsureCapacity((emxArray__common *)EOL, i0, (int)sizeof(double));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  ixstart = X->size[1];
  for (i0 = 0; i0 < ixstart; i0++) {
    EOL->data[i0] = 1.0E+99;
  }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

  emxInit_boolean_T(&B, 2);
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  switch ((int)eml_switch_helper(input)) {
   case 0:
    ThresholdEqnPower(X, B);
    break;

   case 1:
    ThresholdEqnCurrent(X, B);
    break;

   case 2:
    ThresholdEqnResistance(X, B);
    break;

   default:
    for (i0 = 0; i0 < 2; i0++) {
      uv0[i0] = (unsigned int)EOL->size[i0];
    }
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);

    i0 = B->size[0] * B->size[1];
    B->size[0] = 1;
    emxEnsureCapacity((emxArray__common *)B, i0, (int)sizeof(boolean_T));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
    i0 = B->size[0] * B->size[1];
    B->size[1] = (int)uv0[1];
    emxEnsureCapacity((emxArray__common *)B, i0, (int)sizeof(boolean_T));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
    ixstart = (int)uv0[1];
    for (i0 = 0; i0 < ixstart; i0++) {
      B->data[i0] = true;
    }
    break;
  }

// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  for (i0 = 0; i0 < 2; i0++) {
    uv0[i0] = (unsigned int)EOL->size[i0];
  }

// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  emxInit_real_T(&r0, 2);
  i0 = r0->size[0] * r0->size[1];
  r0->size[0] = 1;
  r0->size[1] = (int)uv0[1];
  emxEnsureCapacity((emxArray__common *)r0, i0, (int)sizeof(double));
// OS_printf("R2U2: prognostics: update: %s %d\n",__FILE__,__LINE__);
  for (ixstart = 1; ixstart <= (int)uv0[1]; ixstart++) {
    if (t0 <= 1.0E+99) {
      r0->data[ixstart - 1] = t0;
    } else {
      r0->data[ixstart - 1] = 1.0E+99;
    }
  }

  i0 = EOL->size[0] * EOL->size[1];
  EOL->size[0] = 1;
  EOL->size[1] = r0->size[1];
  emxEnsureCapacity((emxArray__common *)EOL, i0, (int)sizeof(double));
  ixstart = r0->size[0] * r0->size[1];
  for (i0 = 0; i0 < ixstart; i0++) {
    EOL->data[i0] = r0->data[i0] * (double)B->data[i0] + EOL->data[i0] * (double)
      !B->data[i0];
  }

  /*  simulate */
  /* while sum(~P.S.thresholdEqn(t,X,U))>0 && max(EOL)>=1e99 && t<options.tMax */
  emxInit_real_T(&c_X, 2);
  emxInit_real_T(&d_X, 2);
  emxInit_real_T(&e_X, 2);
  do {
    exitg1 = 0;
    ixstart = 1;
    n = EOL->size[1];
    uBlockSize = EOL->data[0];
    if (EOL->size[1] > 1) {
      if (rtIsNaN(EOL->data[0])) {
        ix = 2;
        exitg2 = false;
        while ((!exitg2) && (ix <= n)) {
          ixstart = ix;
          if (!rtIsNaN(EOL->data[ix - 1])) {
            uBlockSize = EOL->data[ix - 1];
            exitg2 = true;
          } else {
            ix++;
          }
        }
      }

      if (ixstart < EOL->size[1]) {
        while (ixstart + 1 <= n) {
          if (EOL->data[ixstart] > uBlockSize) {
            uBlockSize = EOL->data[ixstart];
          }

          ixstart++;
        }
      }
    }

    if ((uBlockSize >= 1.0E+99) && (t < tMax)) {
      /*  keep running until all samples meet threshold or hit tMax */
      switch ((int)eml_switch_helper(input)) {
       case 0:
        i0 = c_X->size[0] * c_X->size[1];
        c_X->size[0] = X->size[0];
        c_X->size[1] = X->size[1];
        emxEnsureCapacity((emxArray__common *)c_X, i0, (int)sizeof(double));
        ixstart = X->size[0] * X->size[1];
        for (i0 = 0; i0 < ixstart; i0++) {
          c_X->data[i0] = X->data[i0];
        }

        StateEqnPower(c_X, U, X);
        break;

       case 1:
        i0 = d_X->size[0] * d_X->size[1];
        d_X->size[0] = X->size[0];
        d_X->size[1] = X->size[1];
        emxEnsureCapacity((emxArray__common *)d_X, i0, (int)sizeof(double));
        ixstart = X->size[0] * X->size[1];
        for (i0 = 0; i0 < ixstart; i0++) {
          d_X->data[i0] = X->data[i0];
        }

        StateEqnCurrent(d_X, U, X);
        break;

       case 2:
        i0 = e_X->size[0] * e_X->size[1];
        e_X->size[0] = X->size[0];
        e_X->size[1] = X->size[1];
        emxEnsureCapacity((emxArray__common *)e_X, i0, (int)sizeof(double));
        ixstart = X->size[0] * X->size[1];
        for (i0 = 0; i0 < ixstart; i0++) {
          e_X->data[i0] = X->data[i0];
        }

        StateEqnResistance(e_X, U, X);
        break;
      }

      /*  update time */
      /* t = round(1/P.sampleTime*(t+P.sampleTime))/(1/P.sampleTime); % this is trick to avoid precision issues */
      t++;

      /*  update EOL values */
      switch ((int)eml_switch_helper(input)) {
       case 0:
        ThresholdEqnPower(X, B);
        break;

       case 1:
        ThresholdEqnCurrent(X, B);
        break;

       case 2:
        ThresholdEqnResistance(X, B);
        break;

       default:
        for (i0 = 0; i0 < 2; i0++) {
          uv0[i0] = (unsigned int)EOL->size[i0];
        }

        i0 = B->size[0] * B->size[1];
        B->size[0] = 1;
        emxEnsureCapacity((emxArray__common *)B, i0, (int)sizeof(boolean_T));
        i0 = B->size[0] * B->size[1];
        B->size[1] = (int)uv0[1];
        emxEnsureCapacity((emxArray__common *)B, i0, (int)sizeof(boolean_T));
        ixstart = (int)uv0[1];
        for (i0 = 0; i0 < ixstart; i0++) {
          B->data[i0] = true;
        }
        break;
      }

      for (i0 = 0; i0 < 2; i0++) {
        uv0[i0] = (unsigned int)EOL->size[i0];
      }

      i0 = r0->size[0] * r0->size[1];
      r0->size[0] = 1;
      r0->size[1] = (int)uv0[1];
      emxEnsureCapacity((emxArray__common *)r0, i0, (int)sizeof(double));
      for (ixstart = 0; ixstart + 1 <= (int)uv0[1]; ixstart++) {
        if ((t <= EOL->data[ixstart]) || rtIsNaN(EOL->data[ixstart])) {
          uBlockSize = t;
        } else {
          uBlockSize = EOL->data[ixstart];
        }

        r0->data[ixstart] = uBlockSize;
      }

      i0 = EOL->size[0] * EOL->size[1];
      EOL->size[0] = 1;
      EOL->size[1] = r0->size[1];
      emxEnsureCapacity((emxArray__common *)EOL, i0, (int)sizeof(double));
      ixstart = r0->size[0] * r0->size[1];
      for (i0 = 0; i0 < ixstart; i0++) {
        EOL->data[i0] = r0->data[i0] * (double)B->data[i0] + EOL->data[i0] *
          (double)!B->data[i0];
      }

      /*  print status */
      if (t - floor(t / 100.0) * 100.0 == 0.0) {
        b_fprintf(t);
      }
    } else {
      exitg1 = 1;
    }
  } while (exitg1 == 0);

  emxFree_real_T(&e_X);
  emxFree_real_T(&d_X);
  emxFree_real_T(&c_X);
  emxFree_real_T(&r0);
  emxFree_boolean_T(&B);
  emxFree_real_T(&U);
  i0 = RUL->size[0] * RUL->size[1];
  RUL->size[0] = 1;
  RUL->size[1] = EOL->size[1];
  emxEnsureCapacity((emxArray__common *)RUL, i0, (int)sizeof(double));
  ixstart = EOL->size[0] * EOL->size[1];
  for (i0 = 0; i0 < ixstart; i0++) {
    RUL->data[i0] = EOL->data[i0] - t0;
  }
}

/*
 * File trailer for CellConstantInputPredict.c
 *
 * [EOF]
 */
