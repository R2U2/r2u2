/*
 * File: StateEqnUKF.c
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
#include "StateEqnUKF.h"
#include "BHM_emxutil.h"
#include "rdivide.h"
#include "asinh.h"
#include "power.h"
#include "log.h"
#include <stdio.h>

/* Function Definitions */

/*
 * This version of the state eqn function does not need P as an argument. It
 *  is needed for the UKF for compilation purposes due to the restrictions on
 *  the use of function handles.
 * Arguments    : const emxArray_real_T *X
 *                const emxArray_real_T *U
 *                double dt
 *                emxArray_real_T *XNew
 * Return Type  : void
 */
void StateEqnUKF(const emxArray_real_T *X, const emxArray_real_T *U, double dt,
                 emxArray_real_T *XNew)
{
  emxArray_real_T *qpS;
  int loop_ub;
  int b_XNew;
  emxArray_real_T *qpB;
  emxArray_real_T *qnB;
  emxArray_real_T *qnS;
  emxArray_real_T *Vo;
  emxArray_real_T *Vsn;
  emxArray_real_T *Vsp;
  emxArray_real_T *Tb;
  emxArray_real_T *xpS;
  emxArray_real_T *r799;
  emxArray_real_T *xnS;
  emxArray_real_T *r800;
  emxArray_real_T *r801;
  emxArray_real_T *r802;
  emxArray_real_T *r803;
  emxArray_real_T *r804;
  emxArray_real_T *r805;
  emxArray_real_T *r806;
  emxArray_real_T *qdotDiffusionBSn;
  emxArray_real_T *xSp;
  emxArray_real_T *r807;
  double VoNominal;
  emxArray_real_T *b;
  emxArray_real_T *r808;
  emxArray_real_T *r809;
  emxArray_real_T *r810;
  unsigned int uv29[2];
  double b_U;
  double c_U;
  emxArray_real_T *b_VoNominal;
  emxArray_real_T *r811;
  emxArray_real_T *b_xpS;
  emxArray_real_T *r812;
  emxArray_real_T *b_xnS;
  emxInit_real_T(&qpS, 2);

  /*  extract states */
  loop_ub = X->size[1];
  b_XNew = qpS->size[0] * qpS->size[1];
  qpS->size[0] = 1;
  qpS->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)qpS, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    qpS->data[qpS->size[0] * b_XNew] = X->data[X->size[0] * b_XNew];
  }

  emxInit_real_T(&qpB, 2);
  loop_ub = X->size[1];
  b_XNew = qpB->size[0] * qpB->size[1];
  qpB->size[0] = 1;
  qpB->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)qpB, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    qpB->data[qpB->size[0] * b_XNew] = X->data[1 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&qnB, 2);
  loop_ub = X->size[1];
  b_XNew = qnB->size[0] * qnB->size[1];
  qnB->size[0] = 1;
  qnB->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)qnB, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    qnB->data[qnB->size[0] * b_XNew] = X->data[2 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&qnS, 2);
  loop_ub = X->size[1];
  b_XNew = qnS->size[0] * qnS->size[1];
  qnS->size[0] = 1;
  qnS->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)qnS, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    qnS->data[qnS->size[0] * b_XNew] = X->data[3 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&Vo, 2);
  loop_ub = X->size[1];
  b_XNew = Vo->size[0] * Vo->size[1];
  Vo->size[0] = 1;
  Vo->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vo, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    Vo->data[Vo->size[0] * b_XNew] = X->data[4 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&Vsn, 2);
  loop_ub = X->size[1];
  b_XNew = Vsn->size[0] * Vsn->size[1];
  Vsn->size[0] = 1;
  Vsn->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsn, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    Vsn->data[Vsn->size[0] * b_XNew] = X->data[5 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&Vsp, 2);
  loop_ub = X->size[1];
  b_XNew = Vsp->size[0] * Vsp->size[1];
  Vsp->size[0] = 1;
  Vsp->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsp, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    Vsp->data[Vsp->size[0] * b_XNew] = X->data[6 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&Tb, 2);
  loop_ub = X->size[1];
  b_XNew = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, b_XNew, (int)sizeof(double));
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    Tb->data[Tb->size[0] * b_XNew] = X->data[7 + X->size[0] * b_XNew];
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r799, 2);

  /*  if qnS<0 */
  /*  	error('qnS<0 at %g',t); */
  /*  elseif qpS>P.qSMax */
  /*  	error('qpS>qSMax at %g',t); */
  /*  end */
  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  rdivide(qpS, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  b_XNew = r799->size[0] * r799->size[1];
  r799->size[0] = 1;
  r799->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r799, b_XNew, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r799->data[b_XNew] = 1.0 - xpS->data[b_XNew];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r800, 2);
  emxInit_real_T(&r801, 2);
  emxInit_real_T(&r802, 2);
  b_rdivide(r799, xpS, r800);
  b_log(r800, r802);

  /*  compute mole fraction at surface, negative electrode */
  rdivide(qnS, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  b_XNew = r801->size[0] * r801->size[1];
  r801->size[0] = 1;
  r801->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r801, b_XNew, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r802);
  emxFree_real_T(&r799);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r801->data[b_XNew] = 1.0 - xnS->data[b_XNew];
  }

  emxInit_real_T(&r803, 2);
  emxInit_real_T(&r804, 2);
  emxInit_real_T(&r805, 2);
  b_rdivide(r801, xnS, r800);
  b_log(r800, r805);

  /*  voltages */
  /*  diffusion: */
  /* 	arrangement is qpS qpB qnB qnS. Current flows from neg to pos so right */
  /* 	to left. Diffusion direction by convention is positive going left to */
  /* 	right. */
  rdivide(qpB, 1.8E-5, r800);
  rdivide(qpS, 2.0000000000000003E-6, r803);
  b_XNew = r804->size[0] * r804->size[1];
  r804->size[0] = 1;
  r804->size[1] = r800->size[1];
  emxEnsureCapacity((emxArray__common *)r804, b_XNew, (int)sizeof(double));
  loop_ub = r800->size[0] * r800->size[1];
  emxFree_real_T(&r805);
  emxFree_real_T(&r801);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r804->data[b_XNew] = r800->data[b_XNew] - r803->data[b_XNew];
  }

  emxInit_real_T(&r806, 2);
  rdivide(r804, 7.0E+6, xnS);
  rdivide(qnB, 1.8E-5, r800);
  rdivide(qnS, 2.0000000000000003E-6, r803);
  b_XNew = r806->size[0] * r806->size[1];
  r806->size[0] = 1;
  r806->size[1] = r800->size[1];
  emxEnsureCapacity((emxArray__common *)r806, b_XNew, (int)sizeof(double));
  loop_ub = r800->size[0] * r800->size[1];
  emxFree_real_T(&r804);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r806->data[b_XNew] = r800->data[b_XNew] - r803->data[b_XNew];
  }

  emxInit_real_T(&qdotDiffusionBSn, 2);
  emxInit_real_T(&xSp, 2);
  emxInit_real_T(&r807, 2);
  rdivide(r806, 7.0E+6, qdotDiffusionBSn);

  /*  charge */
  /*  ohmic drop */
  VoNominal = U->data[0] * 0.117215;

  /*  surface overpotential (Butler-Volmer) */
  rdivide(qnS, 1266.666666666667, xpS);

  /*  mole fraction at neg electrode */
  rdivide(qpS, 11400.0, xSp);

  /*  mole fraction at pos electrode (assume same as bulk) */
  b_XNew = r807->size[0] * r807->size[1];
  r807->size[0] = 1;
  r807->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r807, b_XNew, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r806);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r807->data[b_XNew] = 1.0 - xpS->data[b_XNew];
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r808, 2);
  y_power(r807, b);
  y_power(xpS, r800);
  b_XNew = r808->size[0] * r808->size[1];
  r808->size[0] = 1;
  r808->size[1] = xSp->size[1];
  emxEnsureCapacity((emxArray__common *)r808, b_XNew, (int)sizeof(double));
  loop_ub = xSp->size[0] * xSp->size[1];
  emxFree_real_T(&r807);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r808->data[b_XNew] = 1.0 - xSp->data[b_XNew];
  }

  emxInit_real_T(&r809, 2);
  y_power(r808, xpS);
  y_power(xSp, r803);
  b_XNew = r809->size[0] * r809->size[1];
  r809->size[0] = 1;
  r809->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r809, b_XNew, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r808);
  emxFree_real_T(&xSp);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r809->data[b_XNew] = 2.0 * (2120.96 * b->data[b_XNew] * r800->data[b_XNew]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r810, 2);
  c_rdivide(U->data[0] / 0.000437545, r809, r800);
  b_asinh(r800);
  b_XNew = r810->size[0] * r810->size[1];
  r810->size[0] = 1;
  r810->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r810, b_XNew, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r809);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r810->data[b_XNew] = 2.0 * (248898.0 * xpS->data[b_XNew] * r803->data[b_XNew]);
  }

  c_rdivide(U->data[0] / 0.00030962, r810, r803);
  b_asinh(r803);

  /*  transients */
  /*  temperature */
  /*  assuming constant for now */
  /*  update state */
  emxFree_real_T(&r810);
  for (b_XNew = 0; b_XNew < 2; b_XNew++) {
    uv29[b_XNew] = (unsigned int)X->size[b_XNew];
  }

  b_XNew = XNew->size[0] * XNew->size[1];
  XNew->size[0] = (int)uv29[0];
  emxEnsureCapacity((emxArray__common *)XNew, b_XNew, (int)sizeof(double));
  b_XNew = XNew->size[0] * XNew->size[1];
  XNew->size[1] = (int)uv29[1];
  emxEnsureCapacity((emxArray__common *)XNew, b_XNew, (int)sizeof(double));
  loop_ub = (int)uv29[0] * (int)uv29[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[b_XNew] = 0.0;
  }

  b_U = U->data[0];
  loop_ub = qpS->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[XNew->size[0] * b_XNew] = qpS->data[qpS->size[0] * b_XNew] + (b_U
      + xnS->data[xnS->size[0] * b_XNew]) * dt;
  }

  emxFree_real_T(&qpS);
  b_U = U->data[0];
  c_U = U->data[0];
  loop_ub = qpB->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[1 + XNew->size[0] * b_XNew] = qpB->data[qpB->size[0] * b_XNew] +
      ((-xnS->data[xnS->size[0] * b_XNew] + b_U) - c_U) * dt;
  }

  emxFree_real_T(&qpB);
  b_U = U->data[0] - U->data[0];
  loop_ub = qnB->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[2 + XNew->size[0] * b_XNew] = qnB->data[qnB->size[0] * b_XNew] +
      (b_U - qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * b_XNew]) * dt;
  }

  emxFree_real_T(&qnB);
  b_U = U->data[0];
  loop_ub = qnS->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[3 + XNew->size[0] * b_XNew] = qnS->data[qnS->size[0] * b_XNew] +
      (qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * b_XNew] - b_U) * dt;
  }

  emxFree_real_T(&qdotDiffusionBSn);
  emxFree_real_T(&qnS);
  emxInit_real_T(&b_VoNominal, 2);
  b_XNew = b_VoNominal->size[0] * b_VoNominal->size[1];
  b_VoNominal->size[0] = 1;
  b_VoNominal->size[1] = Vo->size[1];
  emxEnsureCapacity((emxArray__common *)b_VoNominal, b_XNew, (int)sizeof(double));
  loop_ub = Vo->size[0] * Vo->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    b_VoNominal->data[b_XNew] = VoNominal - Vo->data[b_XNew];
  }

  rdivide(b_VoNominal, 6.08671, xnS);
  loop_ub = Vo->size[1];
  emxFree_real_T(&b_VoNominal);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[4 + XNew->size[0] * b_XNew] = Vo->data[Vo->size[0] * b_XNew] +
      xnS->data[xnS->size[0] * b_XNew] * dt;
  }

  emxFree_real_T(&Vo);
  emxInit_real_T(&r811, 2);
  b_XNew = r811->size[0] * r811->size[1];
  r811->size[0] = 1;
  r811->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r811, b_XNew, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r811->data[b_XNew] = 8.3144621 * Tb->data[b_XNew];
  }

  emxInit_real_T(&b_xpS, 2);
  rdivide(r811, 96487.0, xnS);
  rdivide(xnS, 0.5, xpS);
  b_XNew = b_xpS->size[0] * b_xpS->size[1];
  b_xpS->size[0] = 1;
  b_xpS->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)b_xpS, b_XNew, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r811);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    b_xpS->data[b_XNew] = xpS->data[b_XNew] * r800->data[b_XNew] - Vsn->
      data[b_XNew];
  }

  emxFree_real_T(&xpS);
  rdivide(b_xpS, 1001.38, r800);
  loop_ub = Vsn->size[1];
  emxFree_real_T(&b_xpS);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[5 + XNew->size[0] * b_XNew] = Vsn->data[Vsn->size[0] * b_XNew] +
      r800->data[r800->size[0] * b_XNew] * dt;
  }

  emxFree_real_T(&Vsn);
  emxInit_real_T(&r812, 2);
  b_XNew = r812->size[0] * r812->size[1];
  r812->size[0] = 1;
  r812->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r812, b_XNew, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    r812->data[b_XNew] = 8.3144621 * Tb->data[b_XNew];
  }

  emxInit_real_T(&b_xnS, 2);
  rdivide(r812, 96487.0, r800);
  rdivide(r800, 0.5, xnS);
  b_XNew = b_xnS->size[0] * b_xnS->size[1];
  b_xnS->size[0] = 1;
  b_xnS->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)b_xnS, b_XNew, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r812);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    b_xnS->data[b_XNew] = xnS->data[b_XNew] * r803->data[b_XNew] - Vsp->
      data[b_XNew];
  }

  emxFree_real_T(&r803);
  emxFree_real_T(&xnS);
  rdivide(b_xnS, 46.4311, r800);
  loop_ub = Vsp->size[1];
  emxFree_real_T(&b_xnS);
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[6 + XNew->size[0] * b_XNew] = Vsp->data[Vsp->size[0] * b_XNew] +
      r800->data[r800->size[0] * b_XNew] * dt;
  }

  emxFree_real_T(&r800);
  emxFree_real_T(&Vsp);
  VoNominal = 0.0 * dt;
  loop_ub = Tb->size[1];
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[7 + XNew->size[0] * b_XNew] = Tb->data[Tb->size[0] * b_XNew] +
      VoNominal;
  }

  emxFree_real_T(&Tb);

  /*  add process noise */
  b_XNew = XNew->size[0] * XNew->size[1];
  emxEnsureCapacity((emxArray__common *)XNew, b_XNew, (int)sizeof(double));
  loop_ub = XNew->size[0];
  b_XNew = XNew->size[1];
  VoNominal = dt * 0.0;
  loop_ub *= b_XNew;
  for (b_XNew = 0; b_XNew < loop_ub; b_XNew++) {
    XNew->data[b_XNew] += VoNominal;
  }
}

/*
 * File trailer for StateEqnUKF.c
 *
 * [EOF]
 */
