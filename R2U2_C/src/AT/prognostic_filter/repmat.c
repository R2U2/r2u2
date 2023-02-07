/*
 * File: repmat.c
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
#include "repmat.h"
#include "BHM_emxutil.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Arguments    : const emxArray_real_T *a
 *                double varargin_2
 *                emxArray_real_T *b
 * Return Type  : void
 */
void b_repmat(const emxArray_real_T *a, double varargin_2, emxArray_real_T *b)
{
  int outsize_idx_1;
  int jtilecol;
  int ibtile;
  int jcol;
  outsize_idx_1 = a->size[1] * (int)varargin_2;
  jtilecol = b->size[0] * b->size[1];
  b->size[0] = 1;
  b->size[1] = outsize_idx_1;
  emxEnsureCapacity((emxArray__common *)b, jtilecol, (int)sizeof(double));
  if (outsize_idx_1 == 0) {
  } else {
    outsize_idx_1 = a->size[1];
    for (jtilecol = 1; jtilecol <= (int)varargin_2; jtilecol++) {
      ibtile = (jtilecol - 1) * outsize_idx_1;
      for (jcol = 0; jcol + 1 <= outsize_idx_1; jcol++) {
        b->data[ibtile + jcol] = a->data[jcol];
      }
    }
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                double varargin_2
 *                emxArray_real_T *b
 * Return Type  : void
 */
void c_repmat(const emxArray_real_T *a, double varargin_2, emxArray_real_T *b)
{
  int nrows;
  int jtilecol;
  int ibtile;
  int k;
  nrows = b->size[0] * b->size[1];
  b->size[0] = a->size[0];
  b->size[1] = (int)varargin_2;
  emxEnsureCapacity((emxArray__common *)b, nrows, (int)sizeof(double));
  nrows = a->size[0];
  if ((nrows == 0) || ((int)varargin_2 == 0)) {
  } else {
    nrows = a->size[0];
    for (jtilecol = 1; jtilecol <= (int)varargin_2; jtilecol++) {
      ibtile = (jtilecol - 1) * nrows;
      for (k = 1; k <= nrows; k++) {
        b->data[(ibtile + k) - 1] = a->data[k - 1];
      }
    }
  }
}

/*
 * Arguments    : const emxArray_real_T *a
 *                double varargin_2
 *                emxArray_real_T *b
 * Return Type  : void
 */
void repmat(const emxArray_real_T *a, double varargin_2, emxArray_real_T *b)
{
  int outsize_idx_1;
  int nrows;
  int jtilecol;
  int ibtile;
  int jcol;
  int iacol;
  int ibmat;
  int k;
  outsize_idx_1 = a->size[1] * (int)varargin_2;
  nrows = b->size[0] * b->size[1];
  b->size[0] = a->size[0];
  b->size[1] = outsize_idx_1;
  emxEnsureCapacity((emxArray__common *)b, nrows, (int)sizeof(double));
  nrows = a->size[0];
  if ((nrows == 0) || (outsize_idx_1 == 0)) {
  } else {
    nrows = a->size[0];
    outsize_idx_1 = a->size[1];
    for (jtilecol = 1; jtilecol <= (int)varargin_2; jtilecol++) {
      ibtile = (jtilecol - 1) * (nrows * outsize_idx_1) - 1;
      for (jcol = 0; jcol + 1 <= outsize_idx_1; jcol++) {
        iacol = jcol * nrows;
        ibmat = ibtile + jcol * nrows;
        for (k = 1; k <= nrows; k++) {
          b->data[ibmat + k] = a->data[(iacol + k) - 1];
        }
      }
    }
  }
}

/*
 * File trailer for repmat.c
 *
 * [EOF]
 */
