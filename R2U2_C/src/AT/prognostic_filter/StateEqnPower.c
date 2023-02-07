/*
 * File: StateEqnPower.c
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
#include "StateEqnPower.h"
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
void StateEqnPower(const emxArray_real_T *X, const emxArray_real_T *U,
                   emxArray_real_T *XNew)
{
  emxArray_real_T *Vo;
  int loop_ub;
  int i10;
  emxArray_real_T *Vsn;
  emxArray_real_T *Vsp;
  emxArray_real_T *Tb;
  emxArray_real_T *b_X;
  unsigned int uv28[2];
  emxArray_real_T *qnS;
  double extremum;
  emxArray_real_T *c_X;
  emxArray_real_T *qnB;
  emxArray_real_T *d_X;
  emxArray_real_T *qpS;
  emxArray_real_T *e_X;
  emxArray_real_T *qpB;
  emxArray_real_T *xpS;
  emxArray_real_T *r629;
  emxArray_real_T *b;
  emxArray_real_T *r630;
  emxArray_real_T *r631;
  emxArray_real_T *r632;
  emxArray_real_T *r633;
  emxArray_real_T *r634;
  emxArray_real_T *r635;
  emxArray_real_T *r636;
  emxArray_real_T *i;
  emxArray_real_T *r637;
  emxArray_real_T *r638;
  emxArray_real_T *qdotDiffusionBSp;
  emxArray_real_T *r639;
  emxArray_real_T *qdotDiffusionBSn;
  emxArray_real_T *r640;
  emxArray_real_T *r641;
  emxArray_real_T *r642;
  emxArray_real_T *r643;
  emxArray_real_T *r644;
  emxArray_real_T *r645;
  emxArray_real_T *r646;
  emxArray_real_T *r647;
  emxArray_real_T *r648;
  emxArray_real_T *r649;
  emxArray_real_T *r650;
  emxArray_real_T *r651;
  emxArray_real_T *r652;
  emxArray_real_T *r653;
  emxArray_real_T *r654;
  emxArray_real_T *r655;
  emxArray_real_T *r656;
  emxArray_real_T *r657;
  emxArray_real_T *r658;
  emxArray_real_T *r659;
  emxArray_real_T *r660;
  emxArray_real_T *r661;
  emxArray_real_T *r662;
  emxArray_real_T *r663;
  emxArray_real_T *r664;
  emxArray_real_T *r665;
  emxArray_real_T *r666;
  emxArray_real_T *r667;
  emxArray_real_T *r668;
  emxArray_real_T *r669;
  emxArray_real_T *r670;
  emxArray_real_T *r671;
  emxArray_real_T *r672;
  emxArray_real_T *r673;
  emxArray_real_T *r674;
  emxArray_real_T *r675;
  emxArray_real_T *r676;
  emxArray_real_T *r677;
  emxArray_real_T *r678;
  emxArray_real_T *r679;
  emxArray_real_T *r680;
  emxArray_real_T *r681;
  emxArray_real_T *r682;
  emxArray_real_T *r683;
  emxArray_real_T *r684;
  emxArray_real_T *r685;
  emxArray_real_T *xnS;
  emxArray_real_T *r686;
  emxArray_real_T *b_b;
  emxArray_real_T *r687;
  emxArray_real_T *r688;
  emxArray_real_T *r689;
  emxArray_real_T *r690;
  emxArray_real_T *r691;
  emxArray_real_T *r692;
  emxArray_real_T *r693;
  emxArray_real_T *r694;
  emxArray_real_T *r695;
  emxArray_real_T *r696;
  emxArray_real_T *r697;
  emxArray_real_T *r698;
  emxArray_real_T *r699;
  emxArray_real_T *r700;
  emxArray_real_T *r701;
  emxArray_real_T *r702;
  emxArray_real_T *r703;
  emxArray_real_T *r704;
  emxArray_real_T *r705;
  emxArray_real_T *r706;
  emxArray_real_T *r707;
  emxArray_real_T *r708;
  emxArray_real_T *r709;
  emxArray_real_T *r710;
  emxArray_real_T *r711;
  emxArray_real_T *r712;
  emxArray_real_T *r713;
  emxArray_real_T *r714;
  emxArray_real_T *r715;
  emxArray_real_T *r716;
  emxArray_real_T *r717;
  emxArray_real_T *r718;
  emxArray_real_T *r719;
  emxArray_real_T *r720;
  emxArray_real_T *r721;
  emxArray_real_T *r722;
  emxArray_real_T *r723;
  emxArray_real_T *r724;
  emxArray_real_T *r725;
  emxArray_real_T *r726;
  emxArray_real_T *r727;
  emxArray_real_T *r728;
  emxArray_real_T *r729;
  emxArray_real_T *r730;
  emxArray_real_T *r731;
  emxArray_real_T *r732;
  emxArray_real_T *r733;
  emxArray_real_T *r734;
  emxArray_real_T *r735;
  emxArray_real_T *r736;
  emxArray_real_T *r737;
  emxArray_real_T *r738;
  emxArray_real_T *r739;
  emxArray_real_T *r740;
  emxArray_real_T *r741;
  emxArray_real_T *r742;
  emxArray_real_T *r743;
  emxArray_real_T *r744;
  emxArray_real_T *r745;
  emxArray_real_T *r746;
  emxArray_real_T *r747;
  emxArray_real_T *r748;
  emxArray_real_T *xSp;
  emxArray_real_T *r749;
  emxArray_real_T *r750;
  emxArray_real_T *r751;
  emxArray_real_T *r752;
  emxArray_real_T *r753;
  emxArray_real_T *r754;
  emxArray_real_T *r755;
  emxArray_real_T *r756;
  emxArray_real_T *r757;
  emxArray_real_T *r758;
  emxArray_real_T *r759;
  emxArray_real_T *r760;
  emxArray_real_T *r761;
  emxArray_real_T *r762;
  emxArray_real_T *r763;
  emxArray_real_T *r764;
  emxArray_real_T *r765;
  emxArray_real_T *r766;
  emxArray_real_T *r767;
  emxArray_real_T *r768;
  emxArray_real_T *r769;
  emxArray_real_T *r770;
  emxArray_real_T *r771;
  emxArray_real_T *r772;
  emxArray_real_T *r773;
  emxArray_real_T *r774;
  emxArray_real_T *r775;
  emxArray_real_T *r776;
  emxArray_real_T *b_U;
  emxArray_real_T *r777;
  emxArray_real_T *r778;
  emxArray_real_T *r779;
  emxArray_real_T *r780;
  emxArray_real_T *r781;
  emxArray_real_T *r782;
  emxArray_real_T *r783;
  emxArray_real_T *b_i;
  emxArray_real_T *r784;
  emxArray_real_T *c_i;
  emxArray_real_T *r785;
  emxArray_real_T *r786;
  emxInit_real_T(&Vo, 2);
  loop_ub = X->size[1];
  i10 = Vo->size[0] * Vo->size[1];
  Vo->size[0] = 1;
  Vo->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vo, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    Vo->data[Vo->size[0] * i10] = X->data[4 + X->size[0] * i10];
  }

  emxInit_real_T(&Vsn, 2);
  loop_ub = X->size[1];
  i10 = Vsn->size[0] * Vsn->size[1];
  Vsn->size[0] = 1;
  Vsn->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsn, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    Vsn->data[Vsn->size[0] * i10] = X->data[5 + X->size[0] * i10];
  }

  emxInit_real_T(&Vsp, 2);
  loop_ub = X->size[1];
  i10 = Vsp->size[0] * Vsp->size[1];
  Vsp->size[0] = 1;
  Vsp->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsp, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    Vsp->data[Vsp->size[0] * i10] = X->data[6 + X->size[0] * i10];
  }

  emxInit_real_T(&Tb, 2);
  loop_ub = X->size[1];
  i10 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    Tb->data[Tb->size[0] * i10] = X->data[7 + X->size[0] * i10];
  }

  emxInit_real_T(&b_X, 2);

  /*  if qnS<0 */
  /*  %	error('qnS<0 at %g',t); */
  /*  elseif qpS>P.qSMax */
  /*  %	error('qpS>qSMax at %g',t); */
  /*  end */
  /*  state limiting (to prevent C++ code from going into infs/nans, which */
  /*  slows it down considerably) */
  loop_ub = X->size[1];
  i10 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    b_X->data[b_X->size[0] * i10] = X->data[3 + X->size[0] * i10];
  }

  for (i10 = 0; i10 < 2; i10++) {
    uv28[i10] = (unsigned int)b_X->size[i10];
  }

  emxFree_real_T(&b_X);
  emxInit_real_T(&qnS, 2);
  i10 = qnS->size[0] * qnS->size[1];
  qnS->size[0] = 1;
  qnS->size[1] = (int)uv28[1];
  emxEnsureCapacity((emxArray__common *)qnS, i10, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv28[1]; loop_ub++) {
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
  i10 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    c_X->data[c_X->size[0] * i10] = X->data[2 + X->size[0] * i10];
  }

  for (i10 = 0; i10 < 2; i10++) {
    uv28[i10] = (unsigned int)c_X->size[i10];
  }

  emxFree_real_T(&c_X);
  emxInit_real_T(&qnB, 2);
  i10 = qnB->size[0] * qnB->size[1];
  qnB->size[0] = 1;
  qnB->size[1] = (int)uv28[1];
  emxEnsureCapacity((emxArray__common *)qnB, i10, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv28[1]; loop_ub++) {
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
  i10 = d_X->size[0] * d_X->size[1];
  d_X->size[0] = 1;
  d_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)d_X, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    d_X->data[d_X->size[0] * i10] = X->data[X->size[0] * i10];
  }

  for (i10 = 0; i10 < 2; i10++) {
    uv28[i10] = (unsigned int)d_X->size[i10];
  }

  emxFree_real_T(&d_X);
  emxInit_real_T(&qpS, 2);
  i10 = qpS->size[0] * qpS->size[1];
  qpS->size[0] = 1;
  qpS->size[1] = (int)uv28[1];
  emxEnsureCapacity((emxArray__common *)qpS, i10, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv28[1]; loop_ub++) {
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
  i10 = e_X->size[0] * e_X->size[1];
  e_X->size[0] = 1;
  e_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)e_X, i10, (int)sizeof(double));
  for (i10 = 0; i10 < loop_ub; i10++) {
    e_X->data[e_X->size[0] * i10] = X->data[1 + X->size[0] * i10];
  }

  for (i10 = 0; i10 < 2; i10++) {
    uv28[i10] = (unsigned int)e_X->size[i10];
  }

  emxFree_real_T(&e_X);
  emxInit_real_T(&qpB, 2);
  i10 = qpB->size[0] * qpB->size[1];
  qpB->size[0] = 1;
  qpB->size[1] = (int)uv28[1];
  emxEnsureCapacity((emxArray__common *)qpB, i10, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv28[1]; loop_ub++) {
    if ((11399.0 <= X->data[1 + X->size[0] * loop_ub]) || rtIsNaN(X->data[1 +
         X->size[0] * loop_ub])) {
      extremum = 11399.0;
    } else {
      extremum = X->data[1 + X->size[0] * loop_ub];
    }

    qpB->data[loop_ub] = extremum;
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r629, 2);

  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  rdivide(qpS, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i10 = r629->size[0] * r629->size[1];
  r629->size[0] = 1;
  r629->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r629, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    r629->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r630, 2);
  power(r629, b);
  i10 = r630->size[0] * r630->size[1];
  r630->size[0] = 1;
  r630->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r630, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r629);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r630->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r631, 2);
  emxInit_real_T(&r632, 2);
  b_power(r630, r631);
  i10 = r632->size[0] * r632->size[1];
  r632->size[0] = 1;
  r632->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r632, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r630);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r632->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r633, 2);
  emxInit_real_T(&r634, 2);
  c_power(r632, r633);
  i10 = r634->size[0] * r634->size[1];
  r634->size[0] = 1;
  r634->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r634, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r632);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r634->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r635, 2);
  emxInit_real_T(&r636, 2);
  d_power(r634, r635);
  i10 = r636->size[0] * r636->size[1];
  r636->size[0] = 1;
  r636->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r636, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r634);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r636->data[i10] = 2.0 * xpS->data[i10] * 2.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&i, 2);
  emxInit_real_T(&r637, 2);
  b_rdivide(r636, r635, i);
  i10 = r637->size[0] * r637->size[1];
  r637->size[0] = 1;
  r637->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r637, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r636);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r637->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r638, 2);
  e_power(r637, r635);
  i10 = r638->size[0] * r638->size[1];
  r638->size[0] = 1;
  r638->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r638, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r637);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r638->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&qdotDiffusionBSp, 2);
  emxInit_real_T(&r639, 2);
  f_power(r638, qdotDiffusionBSp);
  i10 = r639->size[0] * r639->size[1];
  r639->size[0] = 1;
  r639->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r639, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r638);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r639->data[i10] = 2.0 * xpS->data[i10] * 3.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&qdotDiffusionBSn, 2);
  emxInit_real_T(&r640, 2);
  b_rdivide(r639, qdotDiffusionBSp, qdotDiffusionBSn);
  i10 = r640->size[0] * r640->size[1];
  r640->size[0] = 1;
  r640->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r640, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r639);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r640->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r641, 2);
  g_power(r640, qdotDiffusionBSp);
  i10 = r641->size[0] * r641->size[1];
  r641->size[0] = 1;
  r641->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r641, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r640);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r641->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r642, 2);
  emxInit_real_T(&r643, 2);
  h_power(r641, r642);
  i10 = r643->size[0] * r643->size[1];
  r643->size[0] = 1;
  r643->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r643, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r641);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r643->data[i10] = 2.0 * xpS->data[i10] * 4.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r644, 2);
  emxInit_real_T(&r645, 2);
  b_rdivide(r643, r642, r644);
  i10 = r645->size[0] * r645->size[1];
  r645->size[0] = 1;
  r645->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r645, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r643);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r645->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r646, 2);
  i_power(r645, r642);
  i10 = r646->size[0] * r646->size[1];
  r646->size[0] = 1;
  r646->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r646, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r645);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r646->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r647, 2);
  emxInit_real_T(&r648, 2);
  j_power(r646, r647);
  i10 = r648->size[0] * r648->size[1];
  r648->size[0] = 1;
  r648->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r648, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r646);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r648->data[i10] = 2.0 * xpS->data[i10] * 5.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r649, 2);
  emxInit_real_T(&r650, 2);
  b_rdivide(r648, r647, r649);
  i10 = r650->size[0] * r650->size[1];
  r650->size[0] = 1;
  r650->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r650, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r648);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r650->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r651, 2);
  k_power(r650, r647);
  i10 = r651->size[0] * r651->size[1];
  r651->size[0] = 1;
  r651->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r651, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r650);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r651->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r652, 2);
  emxInit_real_T(&r653, 2);
  l_power(r651, r652);
  i10 = r653->size[0] * r653->size[1];
  r653->size[0] = 1;
  r653->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r653, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r651);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r653->data[i10] = 2.0 * xpS->data[i10] * 6.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r654, 2);
  emxInit_real_T(&r655, 2);
  b_rdivide(r653, r652, r654);
  i10 = r655->size[0] * r655->size[1];
  r655->size[0] = 1;
  r655->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r655, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r653);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r655->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r656, 2);
  m_power(r655, r652);
  i10 = r656->size[0] * r656->size[1];
  r656->size[0] = 1;
  r656->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r656, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r655);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r656->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r657, 2);
  emxInit_real_T(&r658, 2);
  n_power(r656, r657);
  i10 = r658->size[0] * r658->size[1];
  r658->size[0] = 1;
  r658->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r658, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r656);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r658->data[i10] = 2.0 * xpS->data[i10] * 7.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r659, 2);
  emxInit_real_T(&r660, 2);
  b_rdivide(r658, r657, r659);
  i10 = r660->size[0] * r660->size[1];
  r660->size[0] = 1;
  r660->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r660, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r658);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r660->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r661, 2);
  o_power(r660, r657);
  i10 = r661->size[0] * r661->size[1];
  r661->size[0] = 1;
  r661->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r661, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r660);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r661->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r662, 2);
  emxInit_real_T(&r663, 2);
  p_power(r661, r662);
  i10 = r663->size[0] * r663->size[1];
  r663->size[0] = 1;
  r663->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r663, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r661);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r663->data[i10] = 2.0 * xpS->data[i10] * 8.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r664, 2);
  emxInit_real_T(&r665, 2);
  b_rdivide(r663, r662, r664);
  i10 = r665->size[0] * r665->size[1];
  r665->size[0] = 1;
  r665->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r665, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r663);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r665->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r666, 2);
  q_power(r665, r662);
  i10 = r666->size[0] * r666->size[1];
  r666->size[0] = 1;
  r666->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r666, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r665);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r666->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r667, 2);
  emxInit_real_T(&r668, 2);
  r_power(r666, r667);
  i10 = r668->size[0] * r668->size[1];
  r668->size[0] = 1;
  r668->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r668, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r666);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r668->data[i10] = 2.0 * xpS->data[i10] * 9.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r669, 2);
  emxInit_real_T(&r670, 2);
  b_rdivide(r668, r667, r669);
  i10 = r670->size[0] * r670->size[1];
  r670->size[0] = 1;
  r670->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r670, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r668);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r670->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r671, 2);
  s_power(r670, r667);
  i10 = r671->size[0] * r671->size[1];
  r671->size[0] = 1;
  r671->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r671, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r670);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r671->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r672, 2);
  emxInit_real_T(&r673, 2);
  t_power(r671, r672);
  i10 = r673->size[0] * r673->size[1];
  r673->size[0] = 1;
  r673->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r673, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r671);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r673->data[i10] = 2.0 * xpS->data[i10] * 10.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r674, 2);
  emxInit_real_T(&r675, 2);
  b_rdivide(r673, r672, r674);
  i10 = r675->size[0] * r675->size[1];
  r675->size[0] = 1;
  r675->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r675, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r673);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r675->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r676, 2);
  u_power(r675, r672);
  i10 = r676->size[0] * r676->size[1];
  r676->size[0] = 1;
  r676->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r676, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r675);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r676->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r677, 2);
  emxInit_real_T(&r678, 2);
  v_power(r676, r677);
  i10 = r678->size[0] * r678->size[1];
  r678->size[0] = 1;
  r678->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r678, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r676);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r678->data[i10] = 2.0 * xpS->data[i10] * 11.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r679, 2);
  emxInit_real_T(&r680, 2);
  b_rdivide(r678, r677, r679);
  i10 = r680->size[0] * r680->size[1];
  r680->size[0] = 1;
  r680->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r680, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r678);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r680->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r681, 2);
  w_power(r680, r677);
  i10 = r681->size[0] * r681->size[1];
  r681->size[0] = 1;
  r681->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r681, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r680);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r681->data[i10] = 2.0 * xpS->data[i10] - 1.0;
  }

  emxInit_real_T(&r682, 2);
  emxInit_real_T(&r683, 2);
  x_power(r681, r682);
  i10 = r683->size[0] * r683->size[1];
  r683->size[0] = 1;
  r683->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r683, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r681);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r683->data[i10] = 2.0 * xpS->data[i10] * 12.0 * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r684, 2);
  emxInit_real_T(&r685, 2);
  b_rdivide(r683, r682, r684);
  i10 = r685->size[0] * r685->size[1];
  r685->size[0] = 1;
  r685->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r685, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r683);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r685->data[i10] = 1.0 - xpS->data[i10];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r686, 2);
  b_rdivide(r685, xpS, r682);
  c_log(r682);

  /*  compute mole fraction at surface, negative electrode */
  rdivide(qnS, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i10 = r686->size[0] * r686->size[1];
  r686->size[0] = 1;
  r686->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r686, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r685);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r686->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&b_b, 2);
  emxInit_real_T(&r687, 2);
  power(r686, b_b);
  i10 = r687->size[0] * r687->size[1];
  r687->size[0] = 1;
  r687->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r687, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r686);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r687->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r688, 2);
  emxInit_real_T(&r689, 2);
  b_power(r687, r688);
  i10 = r689->size[0] * r689->size[1];
  r689->size[0] = 1;
  r689->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r689, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r687);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r689->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r690, 2);
  emxInit_real_T(&r691, 2);
  c_power(r689, r690);
  i10 = r691->size[0] * r691->size[1];
  r691->size[0] = 1;
  r691->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r691, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r689);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r691->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r692, 2);
  emxInit_real_T(&r693, 2);
  d_power(r691, r692);
  i10 = r693->size[0] * r693->size[1];
  r693->size[0] = 1;
  r693->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r693, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r691);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r693->data[i10] = 2.0 * xnS->data[i10] * 2.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r694, 2);
  emxInit_real_T(&r695, 2);
  b_rdivide(r693, r692, r694);
  i10 = r695->size[0] * r695->size[1];
  r695->size[0] = 1;
  r695->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r695, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r693);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r695->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r696, 2);
  e_power(r695, r692);
  i10 = r696->size[0] * r696->size[1];
  r696->size[0] = 1;
  r696->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r696, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r695);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r696->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r697, 2);
  emxInit_real_T(&r698, 2);
  f_power(r696, r697);
  i10 = r698->size[0] * r698->size[1];
  r698->size[0] = 1;
  r698->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r698, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r696);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r698->data[i10] = 2.0 * xnS->data[i10] * 3.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r699, 2);
  emxInit_real_T(&r700, 2);
  b_rdivide(r698, r697, r699);
  i10 = r700->size[0] * r700->size[1];
  r700->size[0] = 1;
  r700->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r700, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r698);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r700->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r701, 2);
  g_power(r700, r697);
  i10 = r701->size[0] * r701->size[1];
  r701->size[0] = 1;
  r701->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r701, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r700);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r701->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r702, 2);
  emxInit_real_T(&r703, 2);
  h_power(r701, r702);
  i10 = r703->size[0] * r703->size[1];
  r703->size[0] = 1;
  r703->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r703, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r701);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r703->data[i10] = 2.0 * xnS->data[i10] * 4.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r704, 2);
  emxInit_real_T(&r705, 2);
  b_rdivide(r703, r702, r704);
  i10 = r705->size[0] * r705->size[1];
  r705->size[0] = 1;
  r705->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r705, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r703);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r705->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r706, 2);
  i_power(r705, r702);
  i10 = r706->size[0] * r706->size[1];
  r706->size[0] = 1;
  r706->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r706, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r705);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r706->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r707, 2);
  emxInit_real_T(&r708, 2);
  j_power(r706, r707);
  i10 = r708->size[0] * r708->size[1];
  r708->size[0] = 1;
  r708->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r708, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r706);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r708->data[i10] = 2.0 * xnS->data[i10] * 5.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r709, 2);
  emxInit_real_T(&r710, 2);
  b_rdivide(r708, r707, r709);
  i10 = r710->size[0] * r710->size[1];
  r710->size[0] = 1;
  r710->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r710, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r708);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r710->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r711, 2);
  k_power(r710, r707);
  i10 = r711->size[0] * r711->size[1];
  r711->size[0] = 1;
  r711->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r711, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r710);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r711->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r712, 2);
  emxInit_real_T(&r713, 2);
  l_power(r711, r712);
  i10 = r713->size[0] * r713->size[1];
  r713->size[0] = 1;
  r713->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r713, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r711);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r713->data[i10] = 2.0 * xnS->data[i10] * 6.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r714, 2);
  emxInit_real_T(&r715, 2);
  b_rdivide(r713, r712, r714);
  i10 = r715->size[0] * r715->size[1];
  r715->size[0] = 1;
  r715->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r715, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r713);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r715->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r716, 2);
  m_power(r715, r712);
  i10 = r716->size[0] * r716->size[1];
  r716->size[0] = 1;
  r716->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r716, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r715);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r716->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r717, 2);
  emxInit_real_T(&r718, 2);
  n_power(r716, r717);
  i10 = r718->size[0] * r718->size[1];
  r718->size[0] = 1;
  r718->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r718, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r716);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r718->data[i10] = 2.0 * xnS->data[i10] * 7.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r719, 2);
  emxInit_real_T(&r720, 2);
  b_rdivide(r718, r717, r719);
  i10 = r720->size[0] * r720->size[1];
  r720->size[0] = 1;
  r720->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r720, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r718);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r720->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r721, 2);
  o_power(r720, r717);
  i10 = r721->size[0] * r721->size[1];
  r721->size[0] = 1;
  r721->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r721, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r720);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r721->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r722, 2);
  emxInit_real_T(&r723, 2);
  p_power(r721, r722);
  i10 = r723->size[0] * r723->size[1];
  r723->size[0] = 1;
  r723->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r723, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r721);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r723->data[i10] = 2.0 * xnS->data[i10] * 8.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r724, 2);
  emxInit_real_T(&r725, 2);
  b_rdivide(r723, r722, r724);
  i10 = r725->size[0] * r725->size[1];
  r725->size[0] = 1;
  r725->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r725, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r723);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r725->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r726, 2);
  q_power(r725, r722);
  i10 = r726->size[0] * r726->size[1];
  r726->size[0] = 1;
  r726->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r726, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r725);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r726->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r727, 2);
  emxInit_real_T(&r728, 2);
  r_power(r726, r727);
  i10 = r728->size[0] * r728->size[1];
  r728->size[0] = 1;
  r728->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r728, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r726);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r728->data[i10] = 2.0 * xnS->data[i10] * 9.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r729, 2);
  emxInit_real_T(&r730, 2);
  b_rdivide(r728, r727, r729);
  i10 = r730->size[0] * r730->size[1];
  r730->size[0] = 1;
  r730->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r730, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r728);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r730->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r731, 2);
  s_power(r730, r727);
  i10 = r731->size[0] * r731->size[1];
  r731->size[0] = 1;
  r731->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r731, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r730);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r731->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r732, 2);
  emxInit_real_T(&r733, 2);
  t_power(r731, r732);
  i10 = r733->size[0] * r733->size[1];
  r733->size[0] = 1;
  r733->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r733, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r731);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r733->data[i10] = 2.0 * xnS->data[i10] * 10.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r734, 2);
  emxInit_real_T(&r735, 2);
  b_rdivide(r733, r732, r734);
  i10 = r735->size[0] * r735->size[1];
  r735->size[0] = 1;
  r735->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r735, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r733);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r735->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r736, 2);
  u_power(r735, r732);
  i10 = r736->size[0] * r736->size[1];
  r736->size[0] = 1;
  r736->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r736, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r735);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r736->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r737, 2);
  emxInit_real_T(&r738, 2);
  v_power(r736, r737);
  i10 = r738->size[0] * r738->size[1];
  r738->size[0] = 1;
  r738->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r738, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r736);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r738->data[i10] = 2.0 * xnS->data[i10] * 11.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r739, 2);
  emxInit_real_T(&r740, 2);
  b_rdivide(r738, r737, r739);
  i10 = r740->size[0] * r740->size[1];
  r740->size[0] = 1;
  r740->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r740, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r738);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r740->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r741, 2);
  w_power(r740, r737);
  i10 = r741->size[0] * r741->size[1];
  r741->size[0] = 1;
  r741->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r741, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r740);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r741->data[i10] = 2.0 * xnS->data[i10] - 1.0;
  }

  emxInit_real_T(&r742, 2);
  emxInit_real_T(&r743, 2);
  x_power(r741, r742);
  i10 = r743->size[0] * r743->size[1];
  r743->size[0] = 1;
  r743->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r743, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r741);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r743->data[i10] = 2.0 * xnS->data[i10] * 12.0 * (1.0 - xnS->data[i10]);
  }

  emxInit_real_T(&r744, 2);
  emxInit_real_T(&r745, 2);
  b_rdivide(r743, r742, r744);
  i10 = r745->size[0] * r745->size[1];
  r745->size[0] = 1;
  r745->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r745, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r743);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r745->data[i10] = 1.0 - xnS->data[i10];
  }

  emxInit_real_T(&r746, 2);
  b_rdivide(r745, xnS, r742);
  c_log(r742);

  /*  voltages */
  /*  compute current */
  i10 = r746->size[0] * r746->size[1];
  r746->size[0] = 1;
  r746->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r746, i10, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r745);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r746->data[i10] = 8.3144621 * Tb->data[i10];
  }

  emxInit_real_T(&r747, 2);
  emxInit_real_T(&r748, 2);
  rdivide(r746, 96487.0, r747);
  i10 = r748->size[0] * r748->size[1];
  r748->size[0] = 1;
  r748->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r748, i10, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r746);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r748->data[i10] = -31593.7 * b->data[i10];
  }

  emxInit_real_T(&xSp, 2);
  emxInit_real_T(&r749, 2);
  rdivide(r748, 96487.0, xSp);
  i10 = r749->size[0] * r749->size[1];
  r749->size[0] = 1;
  r749->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r749, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r748);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r749->data[i10] = 2.0 * xpS->data[i10] * (1.0 - xpS->data[i10]);
  }

  emxInit_real_T(&r750, 2);
  rdivide(r749, 1.0, xpS);
  i10 = r750->size[0] * r750->size[1];
  r750->size[0] = 1;
  r750->size[1] = r631->size[1];
  emxEnsureCapacity((emxArray__common *)r750, i10, (int)sizeof(double));
  loop_ub = r631->size[0] * r631->size[1];
  emxFree_real_T(&r749);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r750->data[i10] = 0.106747 * (r631->data[i10] - xpS->data[i10]);
  }

  emxInit_real_T(&r751, 2);
  rdivide(r750, 96487.0, r631);
  i10 = r751->size[0] * r751->size[1];
  r751->size[0] = 1;
  r751->size[1] = r633->size[1];
  emxEnsureCapacity((emxArray__common *)r751, i10, (int)sizeof(double));
  loop_ub = r633->size[0] * r633->size[1];
  emxFree_real_T(&r750);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r751->data[i10] = 24606.4 * (r633->data[i10] - i->data[i10]);
  }

  emxInit_real_T(&r752, 2);
  rdivide(r751, 96487.0, r633);
  i10 = r752->size[0] * r752->size[1];
  r752->size[0] = 1;
  r752->size[1] = r635->size[1];
  emxEnsureCapacity((emxArray__common *)r752, i10, (int)sizeof(double));
  loop_ub = r635->size[0] * r635->size[1];
  emxFree_real_T(&r751);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r752->data[i10] = -78561.9 * (r635->data[i10] - qdotDiffusionBSn->data[i10]);
  }

  emxInit_real_T(&r753, 2);
  rdivide(r752, 96487.0, r635);
  i10 = r753->size[0] * r753->size[1];
  r753->size[0] = 1;
  r753->size[1] = qdotDiffusionBSp->size[1];
  emxEnsureCapacity((emxArray__common *)r753, i10, (int)sizeof(double));
  loop_ub = qdotDiffusionBSp->size[0] * qdotDiffusionBSp->size[1];
  emxFree_real_T(&r752);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r753->data[i10] = 13317.9 * (qdotDiffusionBSp->data[i10] - r644->data[i10]);
  }

  emxInit_real_T(&r754, 2);
  rdivide(r753, 96487.0, i);
  i10 = r754->size[0] * r754->size[1];
  r754->size[0] = 1;
  r754->size[1] = r642->size[1];
  emxEnsureCapacity((emxArray__common *)r754, i10, (int)sizeof(double));
  loop_ub = r642->size[0] * r642->size[1];
  emxFree_real_T(&r753);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r754->data[i10] = 307387.0 * (r642->data[i10] - r649->data[i10]);
  }

  emxInit_real_T(&r755, 2);
  rdivide(r754, 96487.0, qdotDiffusionBSp);
  i10 = r755->size[0] * r755->size[1];
  r755->size[0] = 1;
  r755->size[1] = r647->size[1];
  emxEnsureCapacity((emxArray__common *)r755, i10, (int)sizeof(double));
  loop_ub = r647->size[0] * r647->size[1];
  emxFree_real_T(&r754);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r755->data[i10] = 84916.1 * (r647->data[i10] - r654->data[i10]);
  }

  emxInit_real_T(&r756, 2);
  rdivide(r755, 96487.0, qdotDiffusionBSn);
  i10 = r756->size[0] * r756->size[1];
  r756->size[0] = 1;
  r756->size[1] = r652->size[1];
  emxEnsureCapacity((emxArray__common *)r756, i10, (int)sizeof(double));
  loop_ub = r652->size[0] * r652->size[1];
  emxFree_real_T(&r755);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r756->data[i10] = -1.07469E+6 * (r652->data[i10] - r659->data[i10]);
  }

  emxInit_real_T(&r757, 2);
  rdivide(r756, 96487.0, r642);
  i10 = r757->size[0] * r757->size[1];
  r757->size[0] = 1;
  r757->size[1] = r657->size[1];
  emxEnsureCapacity((emxArray__common *)r757, i10, (int)sizeof(double));
  loop_ub = r657->size[0] * r657->size[1];
  emxFree_real_T(&r756);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r757->data[i10] = 2285.04 * (r657->data[i10] - r664->data[i10]);
  }

  emxInit_real_T(&r758, 2);
  rdivide(r757, 96487.0, r644);
  i10 = r758->size[0] * r758->size[1];
  r758->size[0] = 1;
  r758->size[1] = r662->size[1];
  emxEnsureCapacity((emxArray__common *)r758, i10, (int)sizeof(double));
  loop_ub = r662->size[0] * r662->size[1];
  emxFree_real_T(&r757);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r758->data[i10] = 990894.0 * (r662->data[i10] - r669->data[i10]);
  }

  emxInit_real_T(&r759, 2);
  rdivide(r758, 96487.0, r647);
  i10 = r759->size[0] * r759->size[1];
  r759->size[0] = 1;
  r759->size[1] = r667->size[1];
  emxEnsureCapacity((emxArray__common *)r759, i10, (int)sizeof(double));
  loop_ub = r667->size[0] * r667->size[1];
  emxFree_real_T(&r758);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r759->data[i10] = 283920.0 * (r667->data[i10] - r674->data[i10]);
  }

  emxInit_real_T(&r760, 2);
  rdivide(r759, 96487.0, r649);
  i10 = r760->size[0] * r760->size[1];
  r760->size[0] = 1;
  r760->size[1] = r672->size[1];
  emxEnsureCapacity((emxArray__common *)r760, i10, (int)sizeof(double));
  loop_ub = r672->size[0] * r672->size[1];
  emxFree_real_T(&r759);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r760->data[i10] = -161513.0 * (r672->data[i10] - r679->data[i10]);
  }

  emxInit_real_T(&r761, 2);
  rdivide(r760, 96487.0, r652);
  i10 = r761->size[0] * r761->size[1];
  r761->size[0] = 1;
  r761->size[1] = r677->size[1];
  emxEnsureCapacity((emxArray__common *)r761, i10, (int)sizeof(double));
  loop_ub = r677->size[0] * r677->size[1];
  emxFree_real_T(&r760);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r761->data[i10] = -469218.0 * (r677->data[i10] - r684->data[i10]);
  }

  emxInit_real_T(&r762, 2);
  rdivide(r761, 96487.0, r654);
  i10 = r762->size[0] * r762->size[1];
  r762->size[0] = 1;
  r762->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r762, i10, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r761);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r762->data[i10] = 8.3144621 * Tb->data[i10];
  }

  emxInit_real_T(&r763, 2);
  rdivide(r762, 96487.0, r657);
  i10 = r763->size[0] * r763->size[1];
  r763->size[0] = 1;
  r763->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r763, i10, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r762);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r763->data[i10] = 86.19 * b_b->data[i10];
  }

  emxInit_real_T(&r764, 2);
  rdivide(r763, 96487.0, r659);
  i10 = r764->size[0] * r764->size[1];
  r764->size[0] = 1;
  r764->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r764, i10, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r763);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r764->data[i10] = 2.0 * xnS->data[i10] * (1.0 - xnS->data[i10]);
  }

  emxFree_real_T(&xnS);
  emxInit_real_T(&r765, 2);
  rdivide(r764, 1.0, r662);
  i10 = r765->size[0] * r765->size[1];
  r765->size[0] = 1;
  r765->size[1] = r688->size[1];
  emxEnsureCapacity((emxArray__common *)r765, i10, (int)sizeof(double));
  loop_ub = r688->size[0] * r688->size[1];
  emxFree_real_T(&r764);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r765->data[i10] = 0.0 * (r688->data[i10] - r662->data[i10]);
  }

  emxInit_real_T(&r766, 2);
  rdivide(r765, 96487.0, r662);
  i10 = r766->size[0] * r766->size[1];
  r766->size[0] = 1;
  r766->size[1] = r690->size[1];
  emxEnsureCapacity((emxArray__common *)r766, i10, (int)sizeof(double));
  loop_ub = r690->size[0] * r690->size[1];
  emxFree_real_T(&r765);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r766->data[i10] = 0.0 * (r690->data[i10] - r694->data[i10]);
  }

  emxFree_real_T(&r694);
  emxInit_real_T(&r767, 2);
  rdivide(r766, 96487.0, r664);
  i10 = r767->size[0] * r767->size[1];
  r767->size[0] = 1;
  r767->size[1] = r692->size[1];
  emxEnsureCapacity((emxArray__common *)r767, i10, (int)sizeof(double));
  loop_ub = r692->size[0] * r692->size[1];
  emxFree_real_T(&r766);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r767->data[i10] = 0.0 * (r692->data[i10] - r699->data[i10]);
  }

  emxFree_real_T(&r699);
  emxInit_real_T(&r768, 2);
  rdivide(r767, 96487.0, r667);
  i10 = r768->size[0] * r768->size[1];
  r768->size[0] = 1;
  r768->size[1] = r697->size[1];
  emxEnsureCapacity((emxArray__common *)r768, i10, (int)sizeof(double));
  loop_ub = r697->size[0] * r697->size[1];
  emxFree_real_T(&r767);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r768->data[i10] = 0.0 * (r697->data[i10] - r704->data[i10]);
  }

  emxFree_real_T(&r697);
  emxFree_real_T(&r704);
  emxInit_real_T(&r769, 2);
  rdivide(r768, 96487.0, r669);
  i10 = r769->size[0] * r769->size[1];
  r769->size[0] = 1;
  r769->size[1] = r702->size[1];
  emxEnsureCapacity((emxArray__common *)r769, i10, (int)sizeof(double));
  loop_ub = r702->size[0] * r702->size[1];
  emxFree_real_T(&r768);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r769->data[i10] = 0.0 * (r702->data[i10] - r709->data[i10]);
  }

  emxFree_real_T(&r702);
  emxFree_real_T(&r709);
  emxInit_real_T(&r770, 2);
  rdivide(r769, 96487.0, r672);
  i10 = r770->size[0] * r770->size[1];
  r770->size[0] = 1;
  r770->size[1] = r707->size[1];
  emxEnsureCapacity((emxArray__common *)r770, i10, (int)sizeof(double));
  loop_ub = r707->size[0] * r707->size[1];
  emxFree_real_T(&r769);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r770->data[i10] = 0.0 * (r707->data[i10] - r714->data[i10]);
  }

  emxFree_real_T(&r707);
  emxFree_real_T(&r714);
  emxInit_real_T(&r771, 2);
  rdivide(r770, 96487.0, r674);
  i10 = r771->size[0] * r771->size[1];
  r771->size[0] = 1;
  r771->size[1] = r712->size[1];
  emxEnsureCapacity((emxArray__common *)r771, i10, (int)sizeof(double));
  loop_ub = r712->size[0] * r712->size[1];
  emxFree_real_T(&r770);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r771->data[i10] = 0.0 * (r712->data[i10] - r719->data[i10]);
  }

  emxFree_real_T(&r712);
  emxFree_real_T(&r719);
  emxInit_real_T(&r772, 2);
  rdivide(r771, 96487.0, r677);
  i10 = r772->size[0] * r772->size[1];
  r772->size[0] = 1;
  r772->size[1] = r717->size[1];
  emxEnsureCapacity((emxArray__common *)r772, i10, (int)sizeof(double));
  loop_ub = r717->size[0] * r717->size[1];
  emxFree_real_T(&r771);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r772->data[i10] = 0.0 * (r717->data[i10] - r724->data[i10]);
  }

  emxFree_real_T(&r717);
  emxFree_real_T(&r724);
  emxInit_real_T(&r773, 2);
  rdivide(r772, 96487.0, r679);
  i10 = r773->size[0] * r773->size[1];
  r773->size[0] = 1;
  r773->size[1] = r722->size[1];
  emxEnsureCapacity((emxArray__common *)r773, i10, (int)sizeof(double));
  loop_ub = r722->size[0] * r722->size[1];
  emxFree_real_T(&r772);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r773->data[i10] = 0.0 * (r722->data[i10] - r729->data[i10]);
  }

  emxFree_real_T(&r722);
  emxFree_real_T(&r729);
  emxInit_real_T(&r774, 2);
  rdivide(r773, 96487.0, r684);
  i10 = r774->size[0] * r774->size[1];
  r774->size[0] = 1;
  r774->size[1] = r727->size[1];
  emxEnsureCapacity((emxArray__common *)r774, i10, (int)sizeof(double));
  loop_ub = r727->size[0] * r727->size[1];
  emxFree_real_T(&r773);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r774->data[i10] = 0.0 * (r727->data[i10] - r734->data[i10]);
  }

  emxFree_real_T(&r727);
  emxFree_real_T(&r734);
  emxInit_real_T(&r775, 2);
  rdivide(r774, 96487.0, r688);
  i10 = r775->size[0] * r775->size[1];
  r775->size[0] = 1;
  r775->size[1] = r732->size[1];
  emxEnsureCapacity((emxArray__common *)r775, i10, (int)sizeof(double));
  loop_ub = r732->size[0] * r732->size[1];
  emxFree_real_T(&r774);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r775->data[i10] = 0.0 * (r732->data[i10] - r739->data[i10]);
  }

  emxFree_real_T(&r732);
  emxFree_real_T(&r739);
  emxInit_real_T(&r776, 2);
  rdivide(r775, 96487.0, r690);
  i10 = r776->size[0] * r776->size[1];
  r776->size[0] = 1;
  r776->size[1] = r737->size[1];
  emxEnsureCapacity((emxArray__common *)r776, i10, (int)sizeof(double));
  loop_ub = r737->size[0] * r737->size[1];
  emxFree_real_T(&r775);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r776->data[i10] = 0.0 * (r737->data[i10] - r744->data[i10]);
  }

  emxFree_real_T(&r737);
  emxFree_real_T(&r744);
  emxInit_real_T(&b_U, 2);
  rdivide(r776, 96487.0, r692);
  loop_ub = U->size[1];
  i10 = b_U->size[0] * b_U->size[1];
  b_U->size[0] = 1;
  b_U->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_U, i10, (int)sizeof(double));
  emxFree_real_T(&r776);
  for (i10 = 0; i10 < loop_ub; i10++) {
    b_U->data[b_U->size[0] * i10] = U->data[U->size[0] * i10];
  }

  emxInit_real_T(&r777, 2);
  i10 = r777->size[0] * r777->size[1];
  r777->size[0] = 1;
  r777->size[1] = r747->size[1];
  emxEnsureCapacity((emxArray__common *)r777, i10, (int)sizeof(double));
  loop_ub = r747->size[0] * r747->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    r777->data[i10] = (((((((((((((((((4.03 + r747->data[i10] * r682->data[i10])
      + xSp->data[i10]) + r631->data[i10]) + r633->data[i10]) + r635->data[i10])
      + i->data[i10]) + qdotDiffusionBSp->data[i10]) + qdotDiffusionBSn->
      data[i10]) + r642->data[i10]) + r644->data[i10]) + r647->data[i10]) +
      r649->data[i10]) + r652->data[i10]) + r654->data[i10]) -
                         ((((((((((((((0.01 + r657->data[i10] * r742->data[i10])
      + r659->data[i10]) + r662->data[i10]) + r664->data[i10]) + r667->data[i10])
      + r669->data[i10]) + r672->data[i10]) + r674->data[i10]) + r677->data[i10])
      + r679->data[i10]) + r684->data[i10]) + r688->data[i10]) + r690->data[i10])
                          + r692->data[i10])) - Vo->data[i10]) - Vsn->data[i10])
      - Vsp->data[i10];
  }

  emxFree_real_T(&r747);
  emxFree_real_T(&r742);
  emxFree_real_T(&r692);
  emxFree_real_T(&r682);
  emxFree_real_T(&r677);
  emxFree_real_T(&r672);
  emxFree_real_T(&r667);
  emxFree_real_T(&r662);
  emxFree_real_T(&r657);
  emxFree_real_T(&r652);
  emxFree_real_T(&r647);
  emxFree_real_T(&r642);
  emxFree_real_T(&r690);
  emxFree_real_T(&r688);
  emxFree_real_T(&r684);
  emxFree_real_T(&r679);
  emxFree_real_T(&r674);
  emxFree_real_T(&r669);
  emxFree_real_T(&r664);
  emxFree_real_T(&r659);
  emxFree_real_T(&r654);
  emxFree_real_T(&r649);
  emxFree_real_T(&r644);
  emxInit_real_T(&r778, 2);
  b_rdivide(b_U, r777, i);

  /*  diffusion: */
  /* 	arrangement is qpS qpB qnB qnS. Current flows from neg to pos so right */
  /* 	to left. Diffusion direction by convention is positive going left to */
  /* 	right. */
  rdivide(qpB, 1.8E-5, r631);
  rdivide(qpS, 2.0000000000000003E-6, r633);
  i10 = r778->size[0] * r778->size[1];
  r778->size[0] = 1;
  r778->size[1] = r631->size[1];
  emxEnsureCapacity((emxArray__common *)r778, i10, (int)sizeof(double));
  loop_ub = r631->size[0] * r631->size[1];
  emxFree_real_T(&r777);
  emxFree_real_T(&b_U);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r778->data[i10] = r631->data[i10] - r633->data[i10];
  }

  emxInit_real_T(&r779, 2);
  rdivide(r778, 7.0E+6, qdotDiffusionBSp);
  rdivide(qnB, 1.8E-5, r631);
  rdivide(qnS, 2.0000000000000003E-6, r633);
  i10 = r779->size[0] * r779->size[1];
  r779->size[0] = 1;
  r779->size[1] = r631->size[1];
  emxEnsureCapacity((emxArray__common *)r779, i10, (int)sizeof(double));
  loop_ub = r631->size[0] * r631->size[1];
  emxFree_real_T(&r778);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r779->data[i10] = r631->data[i10] - r633->data[i10];
  }

  emxInit_real_T(&r780, 2);
  rdivide(r779, 7.0E+6, qdotDiffusionBSn);

  /*  charge */
  /*  ohmic drop */
  /*  surface overpotential (Butler-Volmer) */
  rdivide(qnS, 1266.666666666667, xpS);

  /*  mole fraction at neg electrode */
  rdivide(qpS, 11400.0, xSp);

  /*  mole fraction at pos electrode (assume same as bulk) */
  i10 = r780->size[0] * r780->size[1];
  r780->size[0] = 1;
  r780->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r780, i10, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r779);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r780->data[i10] = 1.0 - xpS->data[i10];
  }

  emxInit_real_T(&r781, 2);
  y_power(r780, b);
  y_power(xpS, r631);
  i10 = r781->size[0] * r781->size[1];
  r781->size[0] = 1;
  r781->size[1] = xSp->size[1];
  emxEnsureCapacity((emxArray__common *)r781, i10, (int)sizeof(double));
  loop_ub = xSp->size[0] * xSp->size[1];
  emxFree_real_T(&r780);
  emxFree_real_T(&xpS);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r781->data[i10] = 1.0 - xSp->data[i10];
  }

  emxInit_real_T(&r782, 2);
  y_power(r781, b_b);
  y_power(xSp, r633);
  rdivide(i, 0.000437545, r635);
  i10 = r782->size[0] * r782->size[1];
  r782->size[0] = 1;
  r782->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r782, i10, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r781);
  emxFree_real_T(&xSp);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r782->data[i10] = 2.0 * (2120.96 * b->data[i10] * r631->data[i10]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r783, 2);
  b_rdivide(r635, r782, r631);
  b_asinh(r631);
  rdivide(i, 0.00030962, r635);
  i10 = r783->size[0] * r783->size[1];
  r783->size[0] = 1;
  r783->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r783, i10, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r782);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r783->data[i10] = 2.0 * (248898.0 * b_b->data[i10] * r633->data[i10]);
  }

  emxFree_real_T(&b_b);
  b_rdivide(r635, r783, r633);
  b_asinh(r633);

  /*  transients */
  /*  temperature */
  /*  assuming constant for now */
  /*  update state */
  emxFree_real_T(&r783);
  for (i10 = 0; i10 < 2; i10++) {
    uv28[i10] = (unsigned int)X->size[i10];
  }

  i10 = XNew->size[0] * XNew->size[1];
  XNew->size[0] = (int)uv28[0];
  emxEnsureCapacity((emxArray__common *)XNew, i10, (int)sizeof(double));
  i10 = XNew->size[0] * XNew->size[1];
  XNew->size[1] = (int)uv28[1];
  emxEnsureCapacity((emxArray__common *)XNew, i10, (int)sizeof(double));
  loop_ub = (int)uv28[0] * (int)uv28[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[i10] = 0.0;
  }

  loop_ub = qpS->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[XNew->size[0] * i10] = qpS->data[qpS->size[0] * i10] + (i->data
      [i->size[0] * i10] + qdotDiffusionBSp->data[qdotDiffusionBSp->size[0] *
      i10]);
  }

  emxFree_real_T(&qpS);
  loop_ub = qpB->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[1 + XNew->size[0] * i10] = qpB->data[qpB->size[0] * i10] +
      ((-qdotDiffusionBSp->data[qdotDiffusionBSp->size[0] * i10] + i->data
        [i->size[0] * i10]) - i->data[i->size[0] * i10]);
  }

  emxFree_real_T(&qdotDiffusionBSp);
  emxFree_real_T(&qpB);
  loop_ub = qnB->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[2 + XNew->size[0] * i10] = qnB->data[qnB->size[0] * i10] +
      ((i->data[i->size[0] * i10] - i->data[i->size[0] * i10]) -
       qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * i10]);
  }

  emxFree_real_T(&qnB);
  loop_ub = qnS->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[3 + XNew->size[0] * i10] = qnS->data[qnS->size[0] * i10] +
      (qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * i10] - i->data[i->
       size[0] * i10]);
  }

  emxFree_real_T(&qdotDiffusionBSn);
  emxFree_real_T(&qnS);
  emxInit_real_T(&b_i, 2);
  i10 = b_i->size[0] * b_i->size[1];
  b_i->size[0] = 1;
  b_i->size[1] = i->size[1];
  emxEnsureCapacity((emxArray__common *)b_i, i10, (int)sizeof(double));
  loop_ub = i->size[0] * i->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    b_i->data[i10] = i->data[i10] * 0.117215 - Vo->data[i10];
  }

  rdivide(b_i, 6.08671, r635);
  loop_ub = Vo->size[1];
  emxFree_real_T(&b_i);
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[4 + XNew->size[0] * i10] = Vo->data[Vo->size[0] * i10] +
      r635->data[r635->size[0] * i10];
  }

  emxFree_real_T(&Vo);
  emxInit_real_T(&r784, 2);
  i10 = r784->size[0] * r784->size[1];
  r784->size[0] = 1;
  r784->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r784, i10, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    r784->data[i10] = 8.3144621 * Tb->data[i10];
  }

  emxInit_real_T(&c_i, 2);
  rdivide(r784, 96487.0, r635);
  rdivide(r635, 0.5, i);
  i10 = c_i->size[0] * c_i->size[1];
  c_i->size[0] = 1;
  c_i->size[1] = i->size[1];
  emxEnsureCapacity((emxArray__common *)c_i, i10, (int)sizeof(double));
  loop_ub = i->size[0] * i->size[1];
  emxFree_real_T(&r784);
  for (i10 = 0; i10 < loop_ub; i10++) {
    c_i->data[i10] = i->data[i10] * r631->data[i10] - Vsn->data[i10];
  }

  emxFree_real_T(&i);
  rdivide(c_i, 1001.38, r631);
  loop_ub = Vsn->size[1];
  emxFree_real_T(&c_i);
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[5 + XNew->size[0] * i10] = Vsn->data[Vsn->size[0] * i10] +
      r631->data[r631->size[0] * i10];
  }

  emxFree_real_T(&Vsn);
  emxInit_real_T(&r785, 2);
  i10 = r785->size[0] * r785->size[1];
  r785->size[0] = 1;
  r785->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r785, i10, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    r785->data[i10] = 8.3144621 * Tb->data[i10];
  }

  emxInit_real_T(&r786, 2);
  rdivide(r785, 96487.0, r631);
  rdivide(r631, 0.5, r635);
  i10 = r786->size[0] * r786->size[1];
  r786->size[0] = 1;
  r786->size[1] = r635->size[1];
  emxEnsureCapacity((emxArray__common *)r786, i10, (int)sizeof(double));
  loop_ub = r635->size[0] * r635->size[1];
  emxFree_real_T(&r785);
  for (i10 = 0; i10 < loop_ub; i10++) {
    r786->data[i10] = r635->data[i10] * r633->data[i10] - Vsp->data[i10];
  }

  emxFree_real_T(&r635);
  emxFree_real_T(&r633);
  rdivide(r786, 46.4311, r631);
  loop_ub = Vsp->size[1];
  emxFree_real_T(&r786);
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[6 + XNew->size[0] * i10] = Vsp->data[Vsp->size[0] * i10] +
      r631->data[r631->size[0] * i10];
  }

  emxFree_real_T(&r631);
  emxFree_real_T(&Vsp);
  loop_ub = Tb->size[1];
  for (i10 = 0; i10 < loop_ub; i10++) {
    XNew->data[7 + XNew->size[0] * i10] = Tb->data[Tb->size[0] * i10];
  }

  emxFree_real_T(&Tb);

  /*  add process noise */
}

/*
 * File trailer for StateEqnPower.c
 *
 * [EOF]
 */
