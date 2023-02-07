/*
 * File: StateEqnCurrent.c
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
#include "StateEqnCurrent.h"
#include "BHM_emxutil.h"
#include "rdivide.h"
#include "asinh.h"
#include "power.h"
#include "log.h"
#include <stdio.h>

/* Function Definitions */

/*
 * extract states
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *U
 *                emxArray_real_T *XNew
 * Return Type  : void
 */
void StateEqnCurrent(const emxArray_real_T *X, const emxArray_real_T *U,
                     emxArray_real_T *XNew)
{
  emxArray_real_T *Vo;
  int loop_ub;
  int i9;
  emxArray_real_T *Vsn;
  emxArray_real_T *Vsp;
  emxArray_real_T *Tb;
  emxArray_real_T *b_X;
  unsigned int uv27[2];
  emxArray_real_T *qnS;
  double extremum;
  emxArray_real_T *c_X;
  emxArray_real_T *qnB;
  emxArray_real_T *d_X;
  emxArray_real_T *qpS;
  emxArray_real_T *e_X;
  emxArray_real_T *qpB;
  emxArray_real_T *i;
  emxArray_real_T *xpS;
  emxArray_real_T *r615;
  emxArray_real_T *r616;
  emxArray_real_T *r617;
  emxArray_real_T *r618;
  emxArray_real_T *r619;
  emxArray_real_T *r620;
  emxArray_real_T *r621;
  emxArray_real_T *qdotDiffusionBSp;
  emxArray_real_T *r622;
  emxArray_real_T *qdotDiffusionBSn;
  emxArray_real_T *xSp;
  emxArray_real_T *r623;
  emxArray_real_T *b;
  emxArray_real_T *r624;
  emxArray_real_T *r625;
  emxArray_real_T *r626;
  emxArray_real_T *b_i;
  emxArray_real_T *r627;
  emxArray_real_T *b_xpS;
  emxArray_real_T *r628;
  emxArray_real_T *b_xSp;
  emxInit_real_T(&Vo, 2);
  loop_ub = X->size[1];
  i9 = Vo->size[0] * Vo->size[1];
  Vo->size[0] = 1;
  Vo->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vo, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    Vo->data[Vo->size[0] * i9] = X->data[4 + X->size[0] * i9];
  }

  emxInit_real_T(&Vsn, 2);
  loop_ub = X->size[1];
  i9 = Vsn->size[0] * Vsn->size[1];
  Vsn->size[0] = 1;
  Vsn->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsn, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    Vsn->data[Vsn->size[0] * i9] = X->data[5 + X->size[0] * i9];
  }

  emxInit_real_T(&Vsp, 2);
  loop_ub = X->size[1];
  i9 = Vsp->size[0] * Vsp->size[1];
  Vsp->size[0] = 1;
  Vsp->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsp, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    Vsp->data[Vsp->size[0] * i9] = X->data[6 + X->size[0] * i9];
  }

  emxInit_real_T(&Tb, 2);
  loop_ub = X->size[1];
  i9 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    Tb->data[Tb->size[0] * i9] = X->data[7 + X->size[0] * i9];
  }

  emxInit_real_T(&b_X, 2);

  /*  if qnS<0 */
  /*  	error('qnS<0 at %g',t); */
  /*  elseif qpS>P.qSMax */
  /*  	error('qpS>qSMax at %g',t); */
  /*  end */
  /*  state limiting (to prevent C++ code from going into infs/nans, which */
  /*  slows it down considerably) */
  loop_ub = X->size[1];
  i9 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    b_X->data[b_X->size[0] * i9] = X->data[3 + X->size[0] * i9];
  }

  for (i9 = 0; i9 < 2; i9++) {
    uv27[i9] = (unsigned int)b_X->size[i9];
  }

  emxFree_real_T(&b_X);
  emxInit_real_T(&qnS, 2);
  i9 = qnS->size[0] * qnS->size[1];
  qnS->size[0] = 1;
  qnS->size[1] = (int)uv27[1];
  emxEnsureCapacity((emxArray__common *)qnS, i9, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv27[1]; loop_ub++) {
    if ((1.0 >= X->data[3 + X->size[0] * loop_ub]) || rtIsNaN(X->data[3 +
         X->size[0] * loop_ub])) {
      extremum = 1.0;
    } else {
      extremum = X->data[3 + X->size[0] * loop_ub];
    }

    qnS->data[loop_ub] = extremum;
  }

  emxInit_real_T(&c_X, 2);
  loop_ub = X->size[1];
  i9 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    c_X->data[c_X->size[0] * i9] = X->data[2 + X->size[0] * i9];
  }

  for (i9 = 0; i9 < 2; i9++) {
    uv27[i9] = (unsigned int)c_X->size[i9];
  }

  emxFree_real_T(&c_X);
  emxInit_real_T(&qnB, 2);
  i9 = qnB->size[0] * qnB->size[1];
  qnB->size[0] = 1;
  qnB->size[1] = (int)uv27[1];
  emxEnsureCapacity((emxArray__common *)qnB, i9, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv27[1]; loop_ub++) {
    if ((1.0 >= X->data[2 + X->size[0] * loop_ub]) || rtIsNaN(X->data[2 +
         X->size[0] * loop_ub])) {
      extremum = 1.0;
    } else {
      extremum = X->data[2 + X->size[0] * loop_ub];
    }

    qnB->data[loop_ub] = extremum;
  }

  emxInit_real_T(&d_X, 2);
  loop_ub = X->size[1];
  i9 = d_X->size[0] * d_X->size[1];
  d_X->size[0] = 1;
  d_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)d_X, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    d_X->data[d_X->size[0] * i9] = X->data[X->size[0] * i9];
  }

  for (i9 = 0; i9 < 2; i9++) {
    uv27[i9] = (unsigned int)d_X->size[i9];
  }

  emxFree_real_T(&d_X);
  emxInit_real_T(&qpS, 2);
  i9 = qpS->size[0] * qpS->size[1];
  qpS->size[0] = 1;
  qpS->size[1] = (int)uv27[1];
  emxEnsureCapacity((emxArray__common *)qpS, i9, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv27[1]; loop_ub++) {
    if ((1265.666666666667 <= X->data[X->size[0] * loop_ub]) || rtIsNaN(X->
         data[X->size[0] * loop_ub])) {
      extremum = 1265.666666666667;
    } else {
      extremum = X->data[X->size[0] * loop_ub];
    }

    qpS->data[loop_ub] = extremum;
  }

  emxInit_real_T(&e_X, 2);
  loop_ub = X->size[1];
  i9 = e_X->size[0] * e_X->size[1];
  e_X->size[0] = 1;
  e_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)e_X, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    e_X->data[e_X->size[0] * i9] = X->data[1 + X->size[0] * i9];
  }

  for (i9 = 0; i9 < 2; i9++) {
    uv27[i9] = (unsigned int)e_X->size[i9];
  }

  emxFree_real_T(&e_X);
  emxInit_real_T(&qpB, 2);
  i9 = qpB->size[0] * qpB->size[1];
  qpB->size[0] = 1;
  qpB->size[1] = (int)uv27[1];
  emxEnsureCapacity((emxArray__common *)qpB, i9, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv27[1]; loop_ub++) {
    if ((11399.0 <= X->data[1 + X->size[0] * loop_ub]) || rtIsNaN(X->data[1 +
         X->size[0] * loop_ub])) {
      extremum = 11399.0;
    } else {
      extremum = X->data[1 + X->size[0] * loop_ub];
    }

    qpB->data[loop_ub] = extremum;
  }

  emxInit_real_T(&i, 2);

  /*  extract inputs */
  loop_ub = U->size[1];
  i9 = i->size[0] * i->size[1];
  i->size[0] = 1;
  i->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)i, i9, (int)sizeof(double));
  for (i9 = 0; i9 < loop_ub; i9++) {
    i->data[i->size[0] * i9] = U->data[U->size[0] * i9];
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r615, 2);

  /*  compute mole fraction at surface, pos electrode */
  rdivide(qpS, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i9 = r615->size[0] * r615->size[1];
  r615->size[0] = 1;
  r615->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r615, i9, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    r615->data[i9] = 1.0 - xpS->data[i9];
  }

  emxInit_real_T(&r616, 2);
  emxInit_real_T(&r617, 2);
  emxInit_real_T(&r618, 2);
  b_rdivide(r615, xpS, r616);
  b_log(r616, r618);

  /*  compute mole fraction at surface, negative electrode */
  rdivide(qnS, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i9 = r617->size[0] * r617->size[1];
  r617->size[0] = 1;
  r617->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r617, i9, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r618);
  emxFree_real_T(&r615);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r617->data[i9] = 1.0 - xpS->data[i9];
  }

  emxInit_real_T(&r619, 2);
  emxInit_real_T(&r620, 2);
  emxInit_real_T(&r621, 2);
  b_rdivide(r617, xpS, r616);
  b_log(r616, r621);

  /*  voltages */
  /*  diffusion: */
  /* 	arrangement is qpS qpB qnB qnS. Current flows from neg to pos so right */
  /* 	to left. Diffusion direction by convention is positive going left to */
  /* 	right. */
  rdivide(qpB, 1.8E-5, r616);
  rdivide(qpS, 2.0000000000000003E-6, r619);
  i9 = r620->size[0] * r620->size[1];
  r620->size[0] = 1;
  r620->size[1] = r616->size[1];
  emxEnsureCapacity((emxArray__common *)r620, i9, (int)sizeof(double));
  loop_ub = r616->size[0] * r616->size[1];
  emxFree_real_T(&r621);
  emxFree_real_T(&r617);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r620->data[i9] = r616->data[i9] - r619->data[i9];
  }

  emxInit_real_T(&qdotDiffusionBSp, 2);
  emxInit_real_T(&r622, 2);
  rdivide(r620, 7.0E+6, qdotDiffusionBSp);
  rdivide(qnB, 1.8E-5, r616);
  rdivide(qnS, 2.0000000000000003E-6, r619);
  i9 = r622->size[0] * r622->size[1];
  r622->size[0] = 1;
  r622->size[1] = r616->size[1];
  emxEnsureCapacity((emxArray__common *)r622, i9, (int)sizeof(double));
  loop_ub = r616->size[0] * r616->size[1];
  emxFree_real_T(&r620);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r622->data[i9] = r616->data[i9] - r619->data[i9];
  }

  emxInit_real_T(&qdotDiffusionBSn, 2);
  emxInit_real_T(&xSp, 2);
  emxInit_real_T(&r623, 2);
  rdivide(r622, 7.0E+6, qdotDiffusionBSn);

  /*  charge */
  /*  ohmic drop */
  /*  surface overpotential (Butler-Volmer) */
  rdivide(qnS, 1266.666666666667, xpS);

  /*  mole fraction at neg electrode */
  rdivide(qpS, 11400.0, xSp);

  /*  mole fraction at pos electrode (assume same as bulk) */
  i9 = r623->size[0] * r623->size[1];
  r623->size[0] = 1;
  r623->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r623, i9, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r622);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r623->data[i9] = 1.0 - xpS->data[i9];
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r624, 2);
  y_power(r623, b);
  y_power(xpS, r616);
  i9 = r624->size[0] * r624->size[1];
  r624->size[0] = 1;
  r624->size[1] = xSp->size[1];
  emxEnsureCapacity((emxArray__common *)r624, i9, (int)sizeof(double));
  loop_ub = xSp->size[0] * xSp->size[1];
  emxFree_real_T(&r623);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r624->data[i9] = 1.0 - xSp->data[i9];
  }

  emxInit_real_T(&r625, 2);
  y_power(r624, xpS);
  y_power(xSp, r619);
  rdivide(i, 0.000437545, xSp);
  i9 = r625->size[0] * r625->size[1];
  r625->size[0] = 1;
  r625->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r625, i9, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r624);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r625->data[i9] = 2.0 * (2120.96 * b->data[i9] * r616->data[i9]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r626, 2);
  b_rdivide(xSp, r625, r616);
  b_asinh(r616);
  rdivide(i, 0.00030962, xSp);
  i9 = r626->size[0] * r626->size[1];
  r626->size[0] = 1;
  r626->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r626, i9, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r625);
  for (i9 = 0; i9 < loop_ub; i9++) {
    r626->data[i9] = 2.0 * (248898.0 * xpS->data[i9] * r619->data[i9]);
  }

  b_rdivide(xSp, r626, r619);
  b_asinh(r619);

  /*  transients */
  /*  temperature */
  /*  assuming constant for now */
  /*  update state */
  emxFree_real_T(&r626);
  for (i9 = 0; i9 < 2; i9++) {
    uv27[i9] = (unsigned int)X->size[i9];
  }

  i9 = XNew->size[0] * XNew->size[1];
  XNew->size[0] = (int)uv27[0];
  emxEnsureCapacity((emxArray__common *)XNew, i9, (int)sizeof(double));
  i9 = XNew->size[0] * XNew->size[1];
  XNew->size[1] = (int)uv27[1];
  emxEnsureCapacity((emxArray__common *)XNew, i9, (int)sizeof(double));
  loop_ub = (int)uv27[0] * (int)uv27[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[i9] = 0.0;
  }

  loop_ub = qpS->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[XNew->size[0] * i9] = qpS->data[qpS->size[0] * i9] + (i->data
      [i->size[0] * i9] + qdotDiffusionBSp->data[qdotDiffusionBSp->size[0] * i9]);
  }

  emxFree_real_T(&qpS);
  loop_ub = qpB->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[1 + XNew->size[0] * i9] = qpB->data[qpB->size[0] * i9] +
      ((-qdotDiffusionBSp->data[qdotDiffusionBSp->size[0] * i9] + i->data
        [i->size[0] * i9]) - i->data[i->size[0] * i9]);
  }

  emxFree_real_T(&qdotDiffusionBSp);
  emxFree_real_T(&qpB);
  loop_ub = qnB->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[2 + XNew->size[0] * i9] = qnB->data[qnB->size[0] * i9] +
      ((i->data[i->size[0] * i9] - i->data[i->size[0] * i9]) -
       qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * i9]);
  }

  emxFree_real_T(&qnB);
  loop_ub = qnS->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[3 + XNew->size[0] * i9] = qnS->data[qnS->size[0] * i9] +
      (qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * i9] - i->data[i->size
       [0] * i9]);
  }

  emxFree_real_T(&qdotDiffusionBSn);
  emxFree_real_T(&qnS);
  emxInit_real_T(&b_i, 2);
  i9 = b_i->size[0] * b_i->size[1];
  b_i->size[0] = 1;
  b_i->size[1] = i->size[1];
  emxEnsureCapacity((emxArray__common *)b_i, i9, (int)sizeof(double));
  loop_ub = i->size[0] * i->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    b_i->data[i9] = i->data[i9] * 0.117215 - Vo->data[i9];
  }

  emxFree_real_T(&i);
  rdivide(b_i, 6.08671, xSp);
  loop_ub = Vo->size[1];
  emxFree_real_T(&b_i);
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[4 + XNew->size[0] * i9] = Vo->data[Vo->size[0] * i9] + xSp->
      data[xSp->size[0] * i9];
  }

  emxFree_real_T(&Vo);
  emxInit_real_T(&r627, 2);
  i9 = r627->size[0] * r627->size[1];
  r627->size[0] = 1;
  r627->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r627, i9, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    r627->data[i9] = 8.3144621 * Tb->data[i9];
  }

  emxInit_real_T(&b_xpS, 2);
  rdivide(r627, 96487.0, xSp);
  rdivide(xSp, 0.5, xpS);
  i9 = b_xpS->size[0] * b_xpS->size[1];
  b_xpS->size[0] = 1;
  b_xpS->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)b_xpS, i9, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r627);
  for (i9 = 0; i9 < loop_ub; i9++) {
    b_xpS->data[i9] = xpS->data[i9] * r616->data[i9] - Vsn->data[i9];
  }

  emxFree_real_T(&xpS);
  rdivide(b_xpS, 1001.38, r616);
  loop_ub = Vsn->size[1];
  emxFree_real_T(&b_xpS);
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[5 + XNew->size[0] * i9] = Vsn->data[Vsn->size[0] * i9] +
      r616->data[r616->size[0] * i9];
  }

  emxFree_real_T(&Vsn);
  emxInit_real_T(&r628, 2);
  i9 = r628->size[0] * r628->size[1];
  r628->size[0] = 1;
  r628->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r628, i9, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    r628->data[i9] = 8.3144621 * Tb->data[i9];
  }

  emxInit_real_T(&b_xSp, 2);
  rdivide(r628, 96487.0, r616);
  rdivide(r616, 0.5, xSp);
  i9 = b_xSp->size[0] * b_xSp->size[1];
  b_xSp->size[0] = 1;
  b_xSp->size[1] = xSp->size[1];
  emxEnsureCapacity((emxArray__common *)b_xSp, i9, (int)sizeof(double));
  loop_ub = xSp->size[0] * xSp->size[1];
  emxFree_real_T(&r628);
  for (i9 = 0; i9 < loop_ub; i9++) {
    b_xSp->data[i9] = xSp->data[i9] * r619->data[i9] - Vsp->data[i9];
  }

  emxFree_real_T(&r619);
  emxFree_real_T(&xSp);
  rdivide(b_xSp, 46.4311, r616);
  loop_ub = Vsp->size[1];
  emxFree_real_T(&b_xSp);
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[6 + XNew->size[0] * i9] = Vsp->data[Vsp->size[0] * i9] +
      r616->data[r616->size[0] * i9];
  }

  emxFree_real_T(&r616);
  emxFree_real_T(&Vsp);
  loop_ub = Tb->size[1];
  for (i9 = 0; i9 < loop_ub; i9++) {
    XNew->data[7 + XNew->size[0] * i9] = Tb->data[Tb->size[0] * i9];
  }

  emxFree_real_T(&Tb);

  /*  add process noise */
}

/*
 * File trailer for StateEqnCurrent.c
 *
 * [EOF]
 */
