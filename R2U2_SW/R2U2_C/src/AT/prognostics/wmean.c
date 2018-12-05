/*
 * File: wmean.c
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
#include "wmean.h"
#include "BHM_emxutil.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Compute weighted mean of matrix X with weights w. X should be (nx x n)
 *  and w should be a vector.
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *w
 *                emxArray_real_T *mX
 * Return Type  : void
 */
void b_wmean(const emxArray_real_T *X, const emxArray_real_T *w, emxArray_real_T
             *mX)
{
  emxArray_real_T *newX;
  emxArray_real_T *b_X;
  int i18;
  int br;
  int ar;
  int ic;
  emxArray_real_T *b_w;
  emxArray_real_T *b;
  emxArray_real_T *y;
  int ib;
  int ia;
  int k;
  unsigned int unnamed_idx_0;
  int m;

  /*  make sure that if X is a vector, then both X and w are column vectors */
  emxInit_real_T(&newX, 2);
  if (X->size[1] == 1) {
    emxInit_real_T(&b_X, 2);

    /*  then X is a column vector, make it a row vector (for the */
    /*  multiplication) */
    i18 = b_X->size[0] * b_X->size[1];
    b_X->size[0] = X->size[1];
    b_X->size[1] = X->size[0];
    emxEnsureCapacity((emxArray__common *)b_X, i18, (int)sizeof(double));
    br = X->size[0];
    for (i18 = 0; i18 < br; i18++) {
      ar = X->size[1];
      for (ic = 0; ic < ar; ic++) {
        b_X->data[ic + b_X->size[0] * i18] = X->data[i18 + X->size[0] * ic];
      }
    }

    ar = X->size[0];
    i18 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = ar;
    emxEnsureCapacity((emxArray__common *)newX, i18, (int)sizeof(double));
    for (i18 = 0; i18 < ar; i18++) {
      ic = 0;
      while (ic <= 0) {
        newX->data[newX->size[0] * i18] = b_X->data[i18];
        ic = 1;
      }
    }

    emxFree_real_T(&b_X);
  } else {
    i18 = newX->size[0] * newX->size[1];
    newX->size[0] = X->size[0];
    newX->size[1] = X->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i18, (int)sizeof(double));
    br = X->size[0] * X->size[1];
    for (i18 = 0; i18 < br; i18++) {
      newX->data[i18] = X->data[i18];
    }
  }

  b_emxInit_real_T(&b_w, 1);

  /*  then w is a row vector, make it a column vector */
  i18 = b_w->size[0];
  b_w->size[0] = w->size[1];
  emxEnsureCapacity((emxArray__common *)b_w, i18, (int)sizeof(double));
  br = w->size[1];
  for (i18 = 0; i18 < br; i18++) {
    b_w->data[i18] = w->data[w->size[0] * i18];
  }

  emxInit_real_T(&b, 2);
  ar = w->size[1];
  i18 = b->size[0] * b->size[1];
  b->size[0] = ar;
  b->size[1] = 1;
  emxEnsureCapacity((emxArray__common *)b, i18, (int)sizeof(double));
  i18 = 0;
  while (i18 <= 0) {
    for (i18 = 0; i18 < ar; i18++) {
      b->data[i18] = b_w->data[i18];
    }

    i18 = 1;
  }

  emxFree_real_T(&b_w);
  emxInit_real_T(&y, 2);
  if ((newX->size[1] == 1) || (b->size[0] == 1)) {
    i18 = y->size[0] * y->size[1];
    y->size[0] = newX->size[0];
    y->size[1] = b->size[1];
    emxEnsureCapacity((emxArray__common *)y, i18, (int)sizeof(double));
    br = newX->size[0];
    for (i18 = 0; i18 < br; i18++) {
      ar = b->size[1];
      for (ic = 0; ic < ar; ic++) {
        y->data[i18 + y->size[0] * ic] = 0.0;
        ib = newX->size[1];
        for (ia = 0; ia < ib; ia++) {
          y->data[i18 + y->size[0] * ic] += newX->data[i18 + newX->size[0] * ia]
            * b->data[ia + b->size[0] * ic];
        }
      }
    }
  } else {
    k = newX->size[1];
    unnamed_idx_0 = (unsigned int)newX->size[0];
    m = newX->size[0];
    i18 = y->size[0] * y->size[1];
    y->size[0] = (int)unnamed_idx_0;
    emxEnsureCapacity((emxArray__common *)y, i18, (int)sizeof(double));
    i18 = y->size[0] * y->size[1];
    y->size[1] = 1;
    emxEnsureCapacity((emxArray__common *)y, i18, (int)sizeof(double));
    br = (int)unnamed_idx_0;
    for (i18 = 0; i18 < br; i18++) {
      y->data[i18] = 0.0;
    }

    if (newX->size[0] == 0) {
    } else {
      ar = 0;
      while ((m > 0) && (ar <= 0)) {
        for (ic = 1; ic <= m; ic++) {
          y->data[ic - 1] = 0.0;
        }

        ar = m;
      }

      br = 0;
      ar = 0;
      while ((m > 0) && (ar <= 0)) {
        ar = 0;
        i18 = br + k;
        for (ib = br; ib + 1 <= i18; ib++) {
          if (b->data[ib] != 0.0) {
            ia = ar;
            for (ic = 0; ic + 1 <= m; ic++) {
              ia++;
              y->data[ic] += b->data[ib] * newX->data[ia - 1];
            }
          }

          ar += m;
        }

        br += k;
        ar = m;
      }
    }
  }

  emxFree_real_T(&b);
  emxFree_real_T(&newX);
  i18 = mX->size[0] * mX->size[1];
  mX->size[0] = y->size[0];
  mX->size[1] = y->size[1];
  emxEnsureCapacity((emxArray__common *)mX, i18, (int)sizeof(double));
  br = y->size[0] * y->size[1];
  for (i18 = 0; i18 < br; i18++) {
    mX->data[i18] = y->data[i18];
  }

  emxFree_real_T(&y);
}

/*
 * Compute weighted mean of matrix X with weights w. X should be (nx x n)
 *  and w should be a vector.
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *w
 *                double mX_data[]
 *                int mX_size[1]
 * Return Type  : void
 */
void c_wmean(const emxArray_real_T *X, const emxArray_real_T *w, double mX_data[],
             int mX_size[1])
{
  emxArray_real_T *newX;
  emxArray_real_T *b_X;
  int i26;
  int ia;
  int ib;
  emxArray_real_T *b;
  emxArray_real_T *y;
  int ar;
  int k;
  signed char unnamed_idx_0;
  int m;
  int ic;
  int br;

  /*  make sure that if X is a vector, then both X and w are column vectors */
  emxInit_real_T(&newX, 2);
  if (X->size[1] == 1) {
    emxInit_real_T(&b_X, 2);

    /*  then X is a column vector, make it a row vector (for the */
    /*  multiplication) */
    i26 = b_X->size[0] * b_X->size[1];
    b_X->size[0] = X->size[1];
    b_X->size[1] = 2;
    emxEnsureCapacity((emxArray__common *)b_X, i26, (int)sizeof(double));
    for (i26 = 0; i26 < 2; i26++) {
      ia = X->size[1];
      for (ib = 0; ib < ia; ib++) {
        b_X->data[ib + b_X->size[0] * i26] = X->data[i26 + X->size[0] * ib];
      }
    }

    i26 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = 2;
    emxEnsureCapacity((emxArray__common *)newX, i26, (int)sizeof(double));
    for (i26 = 0; i26 < 2; i26++) {
      ib = 0;
      while (ib <= 0) {
        newX->data[newX->size[0] * i26] = b_X->data[i26];
        ib = 1;
      }
    }

    emxFree_real_T(&b_X);
  } else {
    i26 = newX->size[0] * newX->size[1];
    newX->size[0] = 2;
    newX->size[1] = X->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i26, (int)sizeof(double));
    ia = X->size[0] * X->size[1];
    for (i26 = 0; i26 < ia; i26++) {
      newX->data[i26] = X->data[i26];
    }
  }

  b_emxInit_real_T(&b, 1);

  /*  then w is a row vector, make it a column vector */
  i26 = b->size[0];
  b->size[0] = w->size[1];
  emxEnsureCapacity((emxArray__common *)b, i26, (int)sizeof(double));
  ia = w->size[1];
  for (i26 = 0; i26 < ia; i26++) {
    b->data[i26] = w->data[w->size[0] * i26];
  }

  b_emxInit_real_T(&y, 1);
  if ((newX->size[1] == 1) || (b->size[0] == 1)) {
    i26 = y->size[0];
    y->size[0] = newX->size[0];
    emxEnsureCapacity((emxArray__common *)y, i26, (int)sizeof(double));
    ia = newX->size[0];
    for (i26 = 0; i26 < ia; i26++) {
      y->data[i26] = 0.0;
      ar = newX->size[1];
      for (ib = 0; ib < ar; ib++) {
        y->data[i26] += newX->data[i26 + newX->size[0] * ib] * b->data[ib];
      }
    }
  } else {
    k = newX->size[1];
    unnamed_idx_0 = (signed char)newX->size[0];
    m = newX->size[0];
    i26 = y->size[0];
    y->size[0] = unnamed_idx_0;
    emxEnsureCapacity((emxArray__common *)y, i26, (int)sizeof(double));
    ia = unnamed_idx_0;
    for (i26 = 0; i26 < ia; i26++) {
      y->data[i26] = 0.0;
    }

    ar = 0;
    while (ar <= 0) {
      for (ic = 1; ic <= m; ic++) {
        y->data[ic - 1] = 0.0;
      }

      ar = m;
    }

    br = 0;
    ar = 0;
    while (ar <= 0) {
      ar = 0;
      i26 = br + k;
      for (ib = br; ib + 1 <= i26; ib++) {
        if (b->data[ib] != 0.0) {
          ia = ar;
          for (ic = 0; ic + 1 <= m; ic++) {
            ia++;
            y->data[ic] += b->data[ib] * newX->data[ia - 1];
          }
        }

        ar += m;
      }

      br += k;
      ar = m;
    }
  }

  emxFree_real_T(&b);
  emxFree_real_T(&newX);
  mX_size[0] = y->size[0];
  ia = y->size[0];
  for (i26 = 0; i26 < ia; i26++) {
    mX_data[i26] = y->data[i26];
  }

  emxFree_real_T(&y);
}

/*
 * Compute weighted mean of matrix X with weights w. X should be (nx x n)
 *  and w should be a vector.
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *w
 *                emxArray_real_T *mX
 * Return Type  : void
 */
void wmean(const emxArray_real_T *X, const emxArray_real_T *w, emxArray_real_T
           *mX)
{
  emxArray_real_T *newX;
  emxArray_real_T *b_X;
  int i16;
  int ia;
  int ar;
  int ib;
  emxArray_real_T *b;
  int k;
  unsigned int unnamed_idx_0;
  int m;
  int ic;
  int br;

  /*  make sure that if X is a vector, then both X and w are column vectors */
  emxInit_real_T(&newX, 2);
  if (X->size[1] == 1) {
    emxInit_real_T(&b_X, 2);

    /*  then X is a column vector, make it a row vector (for the */
    /*  multiplication) */
    i16 = b_X->size[0] * b_X->size[1];
    b_X->size[0] = X->size[1];
    b_X->size[1] = X->size[0];
    emxEnsureCapacity((emxArray__common *)b_X, i16, (int)sizeof(double));
    ia = X->size[0];
    for (i16 = 0; i16 < ia; i16++) {
      ar = X->size[1];
      for (ib = 0; ib < ar; ib++) {
        b_X->data[ib + b_X->size[0] * i16] = X->data[i16 + X->size[0] * ib];
      }
    }

    ar = X->size[0];
    i16 = newX->size[0] * newX->size[1];
    newX->size[0] = 1;
    newX->size[1] = ar;
    emxEnsureCapacity((emxArray__common *)newX, i16, (int)sizeof(double));
    for (i16 = 0; i16 < ar; i16++) {
      ib = 0;
      while (ib <= 0) {
        newX->data[newX->size[0] * i16] = b_X->data[i16];
        ib = 1;
      }
    }

    emxFree_real_T(&b_X);
  } else {
    i16 = newX->size[0] * newX->size[1];
    newX->size[0] = X->size[0];
    newX->size[1] = X->size[1];
    emxEnsureCapacity((emxArray__common *)newX, i16, (int)sizeof(double));
    ia = X->size[0] * X->size[1];
    for (i16 = 0; i16 < ia; i16++) {
      newX->data[i16] = X->data[i16];
    }
  }

  b_emxInit_real_T(&b, 1);

  /*  then w is a row vector, make it a column vector */
  i16 = b->size[0];
  b->size[0] = w->size[1];
  emxEnsureCapacity((emxArray__common *)b, i16, (int)sizeof(double));
  ia = w->size[1];
  for (i16 = 0; i16 < ia; i16++) {
    b->data[i16] = w->data[w->size[0] * i16];
  }

  if ((newX->size[1] == 1) || (b->size[0] == 1)) {
    i16 = mX->size[0];
    mX->size[0] = newX->size[0];
    emxEnsureCapacity((emxArray__common *)mX, i16, (int)sizeof(double));
    ia = newX->size[0];
    for (i16 = 0; i16 < ia; i16++) {
      mX->data[i16] = 0.0;
      ar = newX->size[1];
      for (ib = 0; ib < ar; ib++) {
        mX->data[i16] += newX->data[i16 + newX->size[0] * ib] * b->data[ib];
      }
    }
  } else {
    k = newX->size[1];
    unnamed_idx_0 = (unsigned int)newX->size[0];
    m = newX->size[0];
    i16 = mX->size[0];
    mX->size[0] = (int)unnamed_idx_0;
    emxEnsureCapacity((emxArray__common *)mX, i16, (int)sizeof(double));
    ia = (int)unnamed_idx_0;
    for (i16 = 0; i16 < ia; i16++) {
      mX->data[i16] = 0.0;
    }

    if (newX->size[0] == 0) {
    } else {
      ar = 0;
      while ((m > 0) && (ar <= 0)) {
        for (ic = 1; ic <= m; ic++) {
          mX->data[ic - 1] = 0.0;
        }

        ar = m;
      }

      br = 0;
      ar = 0;
      while ((m > 0) && (ar <= 0)) {
        ar = -1;
        i16 = br + k;
        for (ib = br; ib + 1 <= i16; ib++) {
          if (b->data[ib] != 0.0) {
            ia = ar;
            for (ic = 0; ic + 1 <= m; ic++) {
              ia++;
              mX->data[ic] += b->data[ib] * newX->data[ia];
            }
          }

          ar += m;
        }

        br += k;
        ar = m;
      }
    }
  }

  emxFree_real_T(&b);
  emxFree_real_T(&newX);
}

/*
 * File trailer for wmean.c
 *
 * [EOF]
 */
