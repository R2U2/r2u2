/*
 * File: StateEqnResistance.c
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
#include "StateEqnResistance.h"
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
void StateEqnResistance(const emxArray_real_T *X, const emxArray_real_T *U,
  emxArray_real_T *XNew)
{
  emxArray_real_T *Vo;
  int loop_ub;
  int i8;
  emxArray_real_T *Vsn;
  emxArray_real_T *Vsp;
  emxArray_real_T *Tb;
  emxArray_real_T *b_X;
  unsigned int uv25[2];
  emxArray_real_T *qnS;
  double extremum;
  emxArray_real_T *c_X;
  emxArray_real_T *qnB;
  emxArray_real_T *d_X;
  emxArray_real_T *qpS;
  emxArray_real_T *e_X;
  emxArray_real_T *qpB;
  emxArray_real_T *xpS;
  emxArray_real_T *r457;
  emxArray_real_T *b;
  emxArray_real_T *r458;
  emxArray_real_T *r459;
  emxArray_real_T *r460;
  emxArray_real_T *r461;
  emxArray_real_T *r462;
  emxArray_real_T *r463;
  emxArray_real_T *r464;
  emxArray_real_T *i;
  emxArray_real_T *r465;
  emxArray_real_T *r466;
  emxArray_real_T *qdotDiffusionBSp;
  emxArray_real_T *r467;
  emxArray_real_T *qdotDiffusionBSn;
  emxArray_real_T *r468;
  emxArray_real_T *r469;
  emxArray_real_T *r470;
  emxArray_real_T *r471;
  emxArray_real_T *r472;
  emxArray_real_T *r473;
  emxArray_real_T *r474;
  emxArray_real_T *r475;
  emxArray_real_T *r476;
  emxArray_real_T *r477;
  emxArray_real_T *r478;
  emxArray_real_T *r479;
  emxArray_real_T *r480;
  emxArray_real_T *r481;
  emxArray_real_T *r482;
  emxArray_real_T *r483;
  emxArray_real_T *r484;
  emxArray_real_T *r485;
  emxArray_real_T *r486;
  emxArray_real_T *r487;
  emxArray_real_T *r488;
  emxArray_real_T *r489;
  emxArray_real_T *r490;
  emxArray_real_T *r491;
  emxArray_real_T *r492;
  emxArray_real_T *r493;
  emxArray_real_T *r494;
  emxArray_real_T *r495;
  emxArray_real_T *r496;
  emxArray_real_T *r497;
  emxArray_real_T *r498;
  emxArray_real_T *r499;
  emxArray_real_T *r500;
  emxArray_real_T *r501;
  emxArray_real_T *r502;
  emxArray_real_T *r503;
  emxArray_real_T *r504;
  emxArray_real_T *r505;
  emxArray_real_T *r506;
  emxArray_real_T *r507;
  emxArray_real_T *r508;
  emxArray_real_T *r509;
  emxArray_real_T *r510;
  emxArray_real_T *r511;
  emxArray_real_T *r512;
  emxArray_real_T *r513;
  emxArray_real_T *xnS;
  emxArray_real_T *r514;
  emxArray_real_T *b_b;
  emxArray_real_T *r515;
  emxArray_real_T *r516;
  emxArray_real_T *r517;
  emxArray_real_T *r518;
  emxArray_real_T *r519;
  emxArray_real_T *r520;
  emxArray_real_T *r521;
  emxArray_real_T *r522;
  emxArray_real_T *r523;
  emxArray_real_T *r524;
  emxArray_real_T *r525;
  emxArray_real_T *r526;
  emxArray_real_T *r527;
  emxArray_real_T *r528;
  emxArray_real_T *r529;
  emxArray_real_T *r530;
  emxArray_real_T *r531;
  emxArray_real_T *r532;
  emxArray_real_T *r533;
  emxArray_real_T *r534;
  emxArray_real_T *r535;
  emxArray_real_T *r536;
  emxArray_real_T *r537;
  emxArray_real_T *r538;
  emxArray_real_T *r539;
  emxArray_real_T *r540;
  emxArray_real_T *r541;
  emxArray_real_T *r542;
  emxArray_real_T *r543;
  emxArray_real_T *r544;
  emxArray_real_T *r545;
  emxArray_real_T *r546;
  emxArray_real_T *r547;
  emxArray_real_T *r548;
  emxArray_real_T *r549;
  emxArray_real_T *r550;
  emxArray_real_T *r551;
  emxArray_real_T *r552;
  emxArray_real_T *r553;
  emxArray_real_T *r554;
  emxArray_real_T *r555;
  emxArray_real_T *r556;
  emxArray_real_T *r557;
  emxArray_real_T *r558;
  emxArray_real_T *r559;
  emxArray_real_T *r560;
  emxArray_real_T *r561;
  emxArray_real_T *r562;
  emxArray_real_T *r563;
  emxArray_real_T *r564;
  emxArray_real_T *r565;
  emxArray_real_T *r566;
  emxArray_real_T *r567;
  emxArray_real_T *r568;
  emxArray_real_T *r569;
  emxArray_real_T *r570;
  emxArray_real_T *r571;
  emxArray_real_T *r572;
  emxArray_real_T *r573;
  emxArray_real_T *r574;
  emxArray_real_T *r575;
  emxArray_real_T *r576;
  emxArray_real_T *xSp;
  emxArray_real_T *r577;
  emxArray_real_T *r578;
  emxArray_real_T *r579;
  emxArray_real_T *r580;
  emxArray_real_T *r581;
  emxArray_real_T *r582;
  emxArray_real_T *r583;
  emxArray_real_T *r584;
  emxArray_real_T *r585;
  emxArray_real_T *r586;
  emxArray_real_T *r587;
  emxArray_real_T *r588;
  emxArray_real_T *r589;
  emxArray_real_T *r590;
  emxArray_real_T *r591;
  emxArray_real_T *r592;
  emxArray_real_T *r593;
  emxArray_real_T *r594;
  emxArray_real_T *r595;
  emxArray_real_T *r596;
  emxArray_real_T *r597;
  emxArray_real_T *r598;
  emxArray_real_T *r599;
  emxArray_real_T *r600;
  emxArray_real_T *r601;
  emxArray_real_T *r602;
  emxArray_real_T *r603;
  emxArray_real_T *r604;
  emxArray_real_T *r605;
  emxArray_real_T *b_U;
  emxArray_real_T *r606;
  emxArray_real_T *r607;
  emxArray_real_T *r608;
  emxArray_real_T *r609;
  emxArray_real_T *r610;
  emxArray_real_T *r611;
  emxArray_real_T *b_i;
  emxArray_real_T *r612;
  emxArray_real_T *c_i;
  emxArray_real_T *r613;
  emxArray_real_T *r614;
  emxInit_real_T(&Vo, 2);
  loop_ub = X->size[1];
  i8 = Vo->size[0] * Vo->size[1];
  Vo->size[0] = 1;
  Vo->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vo, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    Vo->data[Vo->size[0] * i8] = X->data[4 + X->size[0] * i8];
  }

  emxInit_real_T(&Vsn, 2);
  loop_ub = X->size[1];
  i8 = Vsn->size[0] * Vsn->size[1];
  Vsn->size[0] = 1;
  Vsn->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsn, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    Vsn->data[Vsn->size[0] * i8] = X->data[5 + X->size[0] * i8];
  }

  emxInit_real_T(&Vsp, 2);
  loop_ub = X->size[1];
  i8 = Vsp->size[0] * Vsp->size[1];
  Vsp->size[0] = 1;
  Vsp->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Vsp, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    Vsp->data[Vsp->size[0] * i8] = X->data[6 + X->size[0] * i8];
  }

  emxInit_real_T(&Tb, 2);
  loop_ub = X->size[1];
  i8 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    Tb->data[Tb->size[0] * i8] = X->data[7 + X->size[0] * i8];
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
  i8 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    b_X->data[b_X->size[0] * i8] = X->data[3 + X->size[0] * i8];
  }

  for (i8 = 0; i8 < 2; i8++) {
    uv25[i8] = (unsigned int)b_X->size[i8];
  }

  emxFree_real_T(&b_X);
  emxInit_real_T(&qnS, 2);
  i8 = qnS->size[0] * qnS->size[1];
  qnS->size[0] = 1;
  qnS->size[1] = (int)uv25[1];
  emxEnsureCapacity((emxArray__common *)qnS, i8, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv25[1]; loop_ub++) {
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
  i8 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    c_X->data[c_X->size[0] * i8] = X->data[2 + X->size[0] * i8];
  }

  for (i8 = 0; i8 < 2; i8++) {
    uv25[i8] = (unsigned int)c_X->size[i8];
  }

  emxFree_real_T(&c_X);
  emxInit_real_T(&qnB, 2);
  i8 = qnB->size[0] * qnB->size[1];
  qnB->size[0] = 1;
  qnB->size[1] = (int)uv25[1];
  emxEnsureCapacity((emxArray__common *)qnB, i8, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv25[1]; loop_ub++) {
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
  i8 = d_X->size[0] * d_X->size[1];
  d_X->size[0] = 1;
  d_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)d_X, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    d_X->data[d_X->size[0] * i8] = X->data[X->size[0] * i8];
  }

  for (i8 = 0; i8 < 2; i8++) {
    uv25[i8] = (unsigned int)d_X->size[i8];
  }

  emxFree_real_T(&d_X);
  emxInit_real_T(&qpS, 2);
  i8 = qpS->size[0] * qpS->size[1];
  qpS->size[0] = 1;
  qpS->size[1] = (int)uv25[1];
  emxEnsureCapacity((emxArray__common *)qpS, i8, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv25[1]; loop_ub++) {
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
  i8 = e_X->size[0] * e_X->size[1];
  e_X->size[0] = 1;
  e_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)e_X, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    e_X->data[e_X->size[0] * i8] = X->data[1 + X->size[0] * i8];
  }

  for (i8 = 0; i8 < 2; i8++) {
    uv25[i8] = (unsigned int)e_X->size[i8];
  }

  emxFree_real_T(&e_X);
  emxInit_real_T(&qpB, 2);
  i8 = qpB->size[0] * qpB->size[1];
  qpB->size[0] = 1;
  qpB->size[1] = (int)uv25[1];
  emxEnsureCapacity((emxArray__common *)qpB, i8, (int)sizeof(double));
  for (loop_ub = 0; loop_ub + 1 <= (int)uv25[1]; loop_ub++) {
    if ((11399.0 <= X->data[1 + X->size[0] * loop_ub]) || rtIsNaN(X->data[1 +
         X->size[0] * loop_ub])) {
      extremum = 11399.0;
    } else {
      extremum = X->data[1 + X->size[0] * loop_ub];
    }

    qpB->data[loop_ub] = extremum;
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r457, 2);

  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  rdivide(qpS, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i8 = r457->size[0] * r457->size[1];
  r457->size[0] = 1;
  r457->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r457, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    r457->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r458, 2);
  power(r457, b);
  i8 = r458->size[0] * r458->size[1];
  r458->size[0] = 1;
  r458->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r458, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r457);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r458->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r459, 2);
  emxInit_real_T(&r460, 2);
  b_power(r458, r459);
  i8 = r460->size[0] * r460->size[1];
  r460->size[0] = 1;
  r460->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r460, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r458);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r460->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r461, 2);
  emxInit_real_T(&r462, 2);
  c_power(r460, r461);
  i8 = r462->size[0] * r462->size[1];
  r462->size[0] = 1;
  r462->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r462, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r460);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r462->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r463, 2);
  emxInit_real_T(&r464, 2);
  d_power(r462, r463);
  i8 = r464->size[0] * r464->size[1];
  r464->size[0] = 1;
  r464->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r464, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r462);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r464->data[i8] = 2.0 * xpS->data[i8] * 2.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&i, 2);
  emxInit_real_T(&r465, 2);
  b_rdivide(r464, r463, i);
  i8 = r465->size[0] * r465->size[1];
  r465->size[0] = 1;
  r465->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r465, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r464);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r465->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r466, 2);
  e_power(r465, r463);
  i8 = r466->size[0] * r466->size[1];
  r466->size[0] = 1;
  r466->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r466, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r465);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r466->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&qdotDiffusionBSp, 2);
  emxInit_real_T(&r467, 2);
  f_power(r466, qdotDiffusionBSp);
  i8 = r467->size[0] * r467->size[1];
  r467->size[0] = 1;
  r467->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r467, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r466);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r467->data[i8] = 2.0 * xpS->data[i8] * 3.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&qdotDiffusionBSn, 2);
  emxInit_real_T(&r468, 2);
  b_rdivide(r467, qdotDiffusionBSp, qdotDiffusionBSn);
  i8 = r468->size[0] * r468->size[1];
  r468->size[0] = 1;
  r468->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r468, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r467);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r468->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r469, 2);
  g_power(r468, qdotDiffusionBSp);
  i8 = r469->size[0] * r469->size[1];
  r469->size[0] = 1;
  r469->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r469, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r468);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r469->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r470, 2);
  emxInit_real_T(&r471, 2);
  h_power(r469, r470);
  i8 = r471->size[0] * r471->size[1];
  r471->size[0] = 1;
  r471->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r471, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r469);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r471->data[i8] = 2.0 * xpS->data[i8] * 4.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r472, 2);
  emxInit_real_T(&r473, 2);
  b_rdivide(r471, r470, r472);
  i8 = r473->size[0] * r473->size[1];
  r473->size[0] = 1;
  r473->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r473, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r471);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r473->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r474, 2);
  i_power(r473, r470);
  i8 = r474->size[0] * r474->size[1];
  r474->size[0] = 1;
  r474->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r474, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r473);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r474->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r475, 2);
  emxInit_real_T(&r476, 2);
  j_power(r474, r475);
  i8 = r476->size[0] * r476->size[1];
  r476->size[0] = 1;
  r476->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r476, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r474);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r476->data[i8] = 2.0 * xpS->data[i8] * 5.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r477, 2);
  emxInit_real_T(&r478, 2);
  b_rdivide(r476, r475, r477);
  i8 = r478->size[0] * r478->size[1];
  r478->size[0] = 1;
  r478->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r478, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r476);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r478->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r479, 2);
  k_power(r478, r475);
  i8 = r479->size[0] * r479->size[1];
  r479->size[0] = 1;
  r479->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r479, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r478);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r479->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r480, 2);
  emxInit_real_T(&r481, 2);
  l_power(r479, r480);
  i8 = r481->size[0] * r481->size[1];
  r481->size[0] = 1;
  r481->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r481, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r479);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r481->data[i8] = 2.0 * xpS->data[i8] * 6.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r482, 2);
  emxInit_real_T(&r483, 2);
  b_rdivide(r481, r480, r482);
  i8 = r483->size[0] * r483->size[1];
  r483->size[0] = 1;
  r483->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r483, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r481);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r483->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r484, 2);
  m_power(r483, r480);
  i8 = r484->size[0] * r484->size[1];
  r484->size[0] = 1;
  r484->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r484, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r483);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r484->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r485, 2);
  emxInit_real_T(&r486, 2);
  n_power(r484, r485);
  i8 = r486->size[0] * r486->size[1];
  r486->size[0] = 1;
  r486->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r486, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r484);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r486->data[i8] = 2.0 * xpS->data[i8] * 7.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r487, 2);
  emxInit_real_T(&r488, 2);
  b_rdivide(r486, r485, r487);
  i8 = r488->size[0] * r488->size[1];
  r488->size[0] = 1;
  r488->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r488, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r486);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r488->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r489, 2);
  o_power(r488, r485);
  i8 = r489->size[0] * r489->size[1];
  r489->size[0] = 1;
  r489->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r489, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r488);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r489->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r490, 2);
  emxInit_real_T(&r491, 2);
  p_power(r489, r490);
  i8 = r491->size[0] * r491->size[1];
  r491->size[0] = 1;
  r491->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r491, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r489);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r491->data[i8] = 2.0 * xpS->data[i8] * 8.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r492, 2);
  emxInit_real_T(&r493, 2);
  b_rdivide(r491, r490, r492);
  i8 = r493->size[0] * r493->size[1];
  r493->size[0] = 1;
  r493->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r493, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r491);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r493->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r494, 2);
  q_power(r493, r490);
  i8 = r494->size[0] * r494->size[1];
  r494->size[0] = 1;
  r494->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r494, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r493);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r494->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r495, 2);
  emxInit_real_T(&r496, 2);
  r_power(r494, r495);
  i8 = r496->size[0] * r496->size[1];
  r496->size[0] = 1;
  r496->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r496, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r494);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r496->data[i8] = 2.0 * xpS->data[i8] * 9.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r497, 2);
  emxInit_real_T(&r498, 2);
  b_rdivide(r496, r495, r497);
  i8 = r498->size[0] * r498->size[1];
  r498->size[0] = 1;
  r498->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r498, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r496);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r498->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r499, 2);
  s_power(r498, r495);
  i8 = r499->size[0] * r499->size[1];
  r499->size[0] = 1;
  r499->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r499, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r498);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r499->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r500, 2);
  emxInit_real_T(&r501, 2);
  t_power(r499, r500);
  i8 = r501->size[0] * r501->size[1];
  r501->size[0] = 1;
  r501->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r501, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r499);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r501->data[i8] = 2.0 * xpS->data[i8] * 10.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r502, 2);
  emxInit_real_T(&r503, 2);
  b_rdivide(r501, r500, r502);
  i8 = r503->size[0] * r503->size[1];
  r503->size[0] = 1;
  r503->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r503, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r501);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r503->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r504, 2);
  u_power(r503, r500);
  i8 = r504->size[0] * r504->size[1];
  r504->size[0] = 1;
  r504->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r504, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r503);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r504->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r505, 2);
  emxInit_real_T(&r506, 2);
  v_power(r504, r505);
  i8 = r506->size[0] * r506->size[1];
  r506->size[0] = 1;
  r506->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r506, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r504);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r506->data[i8] = 2.0 * xpS->data[i8] * 11.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r507, 2);
  emxInit_real_T(&r508, 2);
  b_rdivide(r506, r505, r507);
  i8 = r508->size[0] * r508->size[1];
  r508->size[0] = 1;
  r508->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r508, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r506);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r508->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r509, 2);
  w_power(r508, r505);
  i8 = r509->size[0] * r509->size[1];
  r509->size[0] = 1;
  r509->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r509, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r508);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r509->data[i8] = 2.0 * xpS->data[i8] - 1.0;
  }

  emxInit_real_T(&r510, 2);
  emxInit_real_T(&r511, 2);
  x_power(r509, r510);
  i8 = r511->size[0] * r511->size[1];
  r511->size[0] = 1;
  r511->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r511, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r509);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r511->data[i8] = 2.0 * xpS->data[i8] * 12.0 * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r512, 2);
  emxInit_real_T(&r513, 2);
  b_rdivide(r511, r510, r512);
  i8 = r513->size[0] * r513->size[1];
  r513->size[0] = 1;
  r513->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r513, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r511);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r513->data[i8] = 1.0 - xpS->data[i8];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r514, 2);
  b_rdivide(r513, xpS, r510);
  c_log(r510);

  /*  compute mole fraction at surface, negative electrode */
  rdivide(qnS, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i8 = r514->size[0] * r514->size[1];
  r514->size[0] = 1;
  r514->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r514, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r513);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r514->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&b_b, 2);
  emxInit_real_T(&r515, 2);
  power(r514, b_b);
  i8 = r515->size[0] * r515->size[1];
  r515->size[0] = 1;
  r515->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r515, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r514);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r515->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r516, 2);
  emxInit_real_T(&r517, 2);
  b_power(r515, r516);
  i8 = r517->size[0] * r517->size[1];
  r517->size[0] = 1;
  r517->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r517, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r515);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r517->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r518, 2);
  emxInit_real_T(&r519, 2);
  c_power(r517, r518);
  i8 = r519->size[0] * r519->size[1];
  r519->size[0] = 1;
  r519->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r519, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r517);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r519->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r520, 2);
  emxInit_real_T(&r521, 2);
  d_power(r519, r520);
  i8 = r521->size[0] * r521->size[1];
  r521->size[0] = 1;
  r521->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r521, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r519);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r521->data[i8] = 2.0 * xnS->data[i8] * 2.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r522, 2);
  emxInit_real_T(&r523, 2);
  b_rdivide(r521, r520, r522);
  i8 = r523->size[0] * r523->size[1];
  r523->size[0] = 1;
  r523->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r523, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r521);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r523->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r524, 2);
  e_power(r523, r520);
  i8 = r524->size[0] * r524->size[1];
  r524->size[0] = 1;
  r524->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r524, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r523);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r524->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r525, 2);
  emxInit_real_T(&r526, 2);
  f_power(r524, r525);
  i8 = r526->size[0] * r526->size[1];
  r526->size[0] = 1;
  r526->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r526, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r524);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r526->data[i8] = 2.0 * xnS->data[i8] * 3.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r527, 2);
  emxInit_real_T(&r528, 2);
  b_rdivide(r526, r525, r527);
  i8 = r528->size[0] * r528->size[1];
  r528->size[0] = 1;
  r528->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r528, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r526);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r528->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r529, 2);
  g_power(r528, r525);
  i8 = r529->size[0] * r529->size[1];
  r529->size[0] = 1;
  r529->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r529, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r528);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r529->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r530, 2);
  emxInit_real_T(&r531, 2);
  h_power(r529, r530);
  i8 = r531->size[0] * r531->size[1];
  r531->size[0] = 1;
  r531->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r531, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r529);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r531->data[i8] = 2.0 * xnS->data[i8] * 4.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r532, 2);
  emxInit_real_T(&r533, 2);
  b_rdivide(r531, r530, r532);
  i8 = r533->size[0] * r533->size[1];
  r533->size[0] = 1;
  r533->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r533, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r531);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r533->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r534, 2);
  i_power(r533, r530);
  i8 = r534->size[0] * r534->size[1];
  r534->size[0] = 1;
  r534->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r534, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r533);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r534->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r535, 2);
  emxInit_real_T(&r536, 2);
  j_power(r534, r535);
  i8 = r536->size[0] * r536->size[1];
  r536->size[0] = 1;
  r536->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r536, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r534);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r536->data[i8] = 2.0 * xnS->data[i8] * 5.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r537, 2);
  emxInit_real_T(&r538, 2);
  b_rdivide(r536, r535, r537);
  i8 = r538->size[0] * r538->size[1];
  r538->size[0] = 1;
  r538->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r538, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r536);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r538->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r539, 2);
  k_power(r538, r535);
  i8 = r539->size[0] * r539->size[1];
  r539->size[0] = 1;
  r539->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r539, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r538);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r539->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r540, 2);
  emxInit_real_T(&r541, 2);
  l_power(r539, r540);
  i8 = r541->size[0] * r541->size[1];
  r541->size[0] = 1;
  r541->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r541, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r539);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r541->data[i8] = 2.0 * xnS->data[i8] * 6.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r542, 2);
  emxInit_real_T(&r543, 2);
  b_rdivide(r541, r540, r542);
  i8 = r543->size[0] * r543->size[1];
  r543->size[0] = 1;
  r543->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r543, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r541);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r543->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r544, 2);
  m_power(r543, r540);
  i8 = r544->size[0] * r544->size[1];
  r544->size[0] = 1;
  r544->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r544, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r543);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r544->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r545, 2);
  emxInit_real_T(&r546, 2);
  n_power(r544, r545);
  i8 = r546->size[0] * r546->size[1];
  r546->size[0] = 1;
  r546->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r546, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r544);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r546->data[i8] = 2.0 * xnS->data[i8] * 7.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r547, 2);
  emxInit_real_T(&r548, 2);
  b_rdivide(r546, r545, r547);
  i8 = r548->size[0] * r548->size[1];
  r548->size[0] = 1;
  r548->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r548, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r546);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r548->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r549, 2);
  o_power(r548, r545);
  i8 = r549->size[0] * r549->size[1];
  r549->size[0] = 1;
  r549->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r549, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r548);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r549->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r550, 2);
  emxInit_real_T(&r551, 2);
  p_power(r549, r550);
  i8 = r551->size[0] * r551->size[1];
  r551->size[0] = 1;
  r551->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r551, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r549);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r551->data[i8] = 2.0 * xnS->data[i8] * 8.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r552, 2);
  emxInit_real_T(&r553, 2);
  b_rdivide(r551, r550, r552);
  i8 = r553->size[0] * r553->size[1];
  r553->size[0] = 1;
  r553->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r553, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r551);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r553->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r554, 2);
  q_power(r553, r550);
  i8 = r554->size[0] * r554->size[1];
  r554->size[0] = 1;
  r554->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r554, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r553);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r554->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r555, 2);
  emxInit_real_T(&r556, 2);
  r_power(r554, r555);
  i8 = r556->size[0] * r556->size[1];
  r556->size[0] = 1;
  r556->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r556, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r554);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r556->data[i8] = 2.0 * xnS->data[i8] * 9.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r557, 2);
  emxInit_real_T(&r558, 2);
  b_rdivide(r556, r555, r557);
  i8 = r558->size[0] * r558->size[1];
  r558->size[0] = 1;
  r558->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r558, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r556);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r558->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r559, 2);
  s_power(r558, r555);
  i8 = r559->size[0] * r559->size[1];
  r559->size[0] = 1;
  r559->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r559, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r558);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r559->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r560, 2);
  emxInit_real_T(&r561, 2);
  t_power(r559, r560);
  i8 = r561->size[0] * r561->size[1];
  r561->size[0] = 1;
  r561->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r561, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r559);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r561->data[i8] = 2.0 * xnS->data[i8] * 10.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r562, 2);
  emxInit_real_T(&r563, 2);
  b_rdivide(r561, r560, r562);
  i8 = r563->size[0] * r563->size[1];
  r563->size[0] = 1;
  r563->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r563, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r561);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r563->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r564, 2);
  u_power(r563, r560);
  i8 = r564->size[0] * r564->size[1];
  r564->size[0] = 1;
  r564->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r564, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r563);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r564->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r565, 2);
  emxInit_real_T(&r566, 2);
  v_power(r564, r565);
  i8 = r566->size[0] * r566->size[1];
  r566->size[0] = 1;
  r566->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r566, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r564);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r566->data[i8] = 2.0 * xnS->data[i8] * 11.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r567, 2);
  emxInit_real_T(&r568, 2);
  b_rdivide(r566, r565, r567);
  i8 = r568->size[0] * r568->size[1];
  r568->size[0] = 1;
  r568->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r568, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r566);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r568->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r569, 2);
  w_power(r568, r565);
  i8 = r569->size[0] * r569->size[1];
  r569->size[0] = 1;
  r569->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r569, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r568);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r569->data[i8] = 2.0 * xnS->data[i8] - 1.0;
  }

  emxInit_real_T(&r570, 2);
  emxInit_real_T(&r571, 2);
  x_power(r569, r570);
  i8 = r571->size[0] * r571->size[1];
  r571->size[0] = 1;
  r571->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r571, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r569);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r571->data[i8] = 2.0 * xnS->data[i8] * 12.0 * (1.0 - xnS->data[i8]);
  }

  emxInit_real_T(&r572, 2);
  emxInit_real_T(&r573, 2);
  b_rdivide(r571, r570, r572);
  i8 = r573->size[0] * r573->size[1];
  r573->size[0] = 1;
  r573->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r573, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r571);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r573->data[i8] = 1.0 - xnS->data[i8];
  }

  emxInit_real_T(&r574, 2);
  b_rdivide(r573, xnS, r570);
  c_log(r570);

  /*  voltages */
  /*  compute current */
  i8 = r574->size[0] * r574->size[1];
  r574->size[0] = 1;
  r574->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r574, i8, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r573);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r574->data[i8] = 8.3144621 * Tb->data[i8];
  }

  emxInit_real_T(&r575, 2);
  emxInit_real_T(&r576, 2);
  rdivide(r574, 96487.0, r575);
  i8 = r576->size[0] * r576->size[1];
  r576->size[0] = 1;
  r576->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r576, i8, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r574);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r576->data[i8] = -31593.7 * b->data[i8];
  }

  emxInit_real_T(&xSp, 2);
  emxInit_real_T(&r577, 2);
  rdivide(r576, 96487.0, xSp);
  i8 = r577->size[0] * r577->size[1];
  r577->size[0] = 1;
  r577->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r577, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r576);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r577->data[i8] = 2.0 * xpS->data[i8] * (1.0 - xpS->data[i8]);
  }

  emxInit_real_T(&r578, 2);
  rdivide(r577, 1.0, xpS);
  i8 = r578->size[0] * r578->size[1];
  r578->size[0] = 1;
  r578->size[1] = r459->size[1];
  emxEnsureCapacity((emxArray__common *)r578, i8, (int)sizeof(double));
  loop_ub = r459->size[0] * r459->size[1];
  emxFree_real_T(&r577);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r578->data[i8] = 0.106747 * (r459->data[i8] - xpS->data[i8]);
  }

  emxInit_real_T(&r579, 2);
  rdivide(r578, 96487.0, r459);
  i8 = r579->size[0] * r579->size[1];
  r579->size[0] = 1;
  r579->size[1] = r461->size[1];
  emxEnsureCapacity((emxArray__common *)r579, i8, (int)sizeof(double));
  loop_ub = r461->size[0] * r461->size[1];
  emxFree_real_T(&r578);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r579->data[i8] = 24606.4 * (r461->data[i8] - i->data[i8]);
  }

  emxInit_real_T(&r580, 2);
  rdivide(r579, 96487.0, r461);
  i8 = r580->size[0] * r580->size[1];
  r580->size[0] = 1;
  r580->size[1] = r463->size[1];
  emxEnsureCapacity((emxArray__common *)r580, i8, (int)sizeof(double));
  loop_ub = r463->size[0] * r463->size[1];
  emxFree_real_T(&r579);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r580->data[i8] = -78561.9 * (r463->data[i8] - qdotDiffusionBSn->data[i8]);
  }

  emxInit_real_T(&r581, 2);
  rdivide(r580, 96487.0, r463);
  i8 = r581->size[0] * r581->size[1];
  r581->size[0] = 1;
  r581->size[1] = qdotDiffusionBSp->size[1];
  emxEnsureCapacity((emxArray__common *)r581, i8, (int)sizeof(double));
  loop_ub = qdotDiffusionBSp->size[0] * qdotDiffusionBSp->size[1];
  emxFree_real_T(&r580);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r581->data[i8] = 13317.9 * (qdotDiffusionBSp->data[i8] - r472->data[i8]);
  }

  emxInit_real_T(&r582, 2);
  rdivide(r581, 96487.0, i);
  i8 = r582->size[0] * r582->size[1];
  r582->size[0] = 1;
  r582->size[1] = r470->size[1];
  emxEnsureCapacity((emxArray__common *)r582, i8, (int)sizeof(double));
  loop_ub = r470->size[0] * r470->size[1];
  emxFree_real_T(&r581);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r582->data[i8] = 307387.0 * (r470->data[i8] - r477->data[i8]);
  }

  emxInit_real_T(&r583, 2);
  rdivide(r582, 96487.0, qdotDiffusionBSp);
  i8 = r583->size[0] * r583->size[1];
  r583->size[0] = 1;
  r583->size[1] = r475->size[1];
  emxEnsureCapacity((emxArray__common *)r583, i8, (int)sizeof(double));
  loop_ub = r475->size[0] * r475->size[1];
  emxFree_real_T(&r582);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r583->data[i8] = 84916.1 * (r475->data[i8] - r482->data[i8]);
  }

  emxInit_real_T(&r584, 2);
  rdivide(r583, 96487.0, qdotDiffusionBSn);
  i8 = r584->size[0] * r584->size[1];
  r584->size[0] = 1;
  r584->size[1] = r480->size[1];
  emxEnsureCapacity((emxArray__common *)r584, i8, (int)sizeof(double));
  loop_ub = r480->size[0] * r480->size[1];
  emxFree_real_T(&r583);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r584->data[i8] = -1.07469E+6 * (r480->data[i8] - r487->data[i8]);
  }

  emxInit_real_T(&r585, 2);
  rdivide(r584, 96487.0, r470);
  i8 = r585->size[0] * r585->size[1];
  r585->size[0] = 1;
  r585->size[1] = r485->size[1];
  emxEnsureCapacity((emxArray__common *)r585, i8, (int)sizeof(double));
  loop_ub = r485->size[0] * r485->size[1];
  emxFree_real_T(&r584);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r585->data[i8] = 2285.04 * (r485->data[i8] - r492->data[i8]);
  }

  emxInit_real_T(&r586, 2);
  rdivide(r585, 96487.0, r472);
  i8 = r586->size[0] * r586->size[1];
  r586->size[0] = 1;
  r586->size[1] = r490->size[1];
  emxEnsureCapacity((emxArray__common *)r586, i8, (int)sizeof(double));
  loop_ub = r490->size[0] * r490->size[1];
  emxFree_real_T(&r585);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r586->data[i8] = 990894.0 * (r490->data[i8] - r497->data[i8]);
  }

  emxInit_real_T(&r587, 2);
  rdivide(r586, 96487.0, r475);
  i8 = r587->size[0] * r587->size[1];
  r587->size[0] = 1;
  r587->size[1] = r495->size[1];
  emxEnsureCapacity((emxArray__common *)r587, i8, (int)sizeof(double));
  loop_ub = r495->size[0] * r495->size[1];
  emxFree_real_T(&r586);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r587->data[i8] = 283920.0 * (r495->data[i8] - r502->data[i8]);
  }

  emxInit_real_T(&r588, 2);
  rdivide(r587, 96487.0, r477);
  i8 = r588->size[0] * r588->size[1];
  r588->size[0] = 1;
  r588->size[1] = r500->size[1];
  emxEnsureCapacity((emxArray__common *)r588, i8, (int)sizeof(double));
  loop_ub = r500->size[0] * r500->size[1];
  emxFree_real_T(&r587);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r588->data[i8] = -161513.0 * (r500->data[i8] - r507->data[i8]);
  }

  emxInit_real_T(&r589, 2);
  rdivide(r588, 96487.0, r480);
  i8 = r589->size[0] * r589->size[1];
  r589->size[0] = 1;
  r589->size[1] = r505->size[1];
  emxEnsureCapacity((emxArray__common *)r589, i8, (int)sizeof(double));
  loop_ub = r505->size[0] * r505->size[1];
  emxFree_real_T(&r588);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r589->data[i8] = -469218.0 * (r505->data[i8] - r512->data[i8]);
  }

  emxInit_real_T(&r590, 2);
  rdivide(r589, 96487.0, r482);
  i8 = r590->size[0] * r590->size[1];
  r590->size[0] = 1;
  r590->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r590, i8, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r589);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r590->data[i8] = 8.3144621 * Tb->data[i8];
  }

  emxInit_real_T(&r591, 2);
  rdivide(r590, 96487.0, r485);
  i8 = r591->size[0] * r591->size[1];
  r591->size[0] = 1;
  r591->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r591, i8, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r590);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r591->data[i8] = 86.19 * b_b->data[i8];
  }

  emxInit_real_T(&r592, 2);
  rdivide(r591, 96487.0, r487);
  i8 = r592->size[0] * r592->size[1];
  r592->size[0] = 1;
  r592->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r592, i8, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r591);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r592->data[i8] = 2.0 * xnS->data[i8] * (1.0 - xnS->data[i8]);
  }

  emxFree_real_T(&xnS);
  emxInit_real_T(&r593, 2);
  rdivide(r592, 1.0, r490);
  i8 = r593->size[0] * r593->size[1];
  r593->size[0] = 1;
  r593->size[1] = r516->size[1];
  emxEnsureCapacity((emxArray__common *)r593, i8, (int)sizeof(double));
  loop_ub = r516->size[0] * r516->size[1];
  emxFree_real_T(&r592);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r593->data[i8] = 0.0 * (r516->data[i8] - r490->data[i8]);
  }

  emxInit_real_T(&r594, 2);
  rdivide(r593, 96487.0, r490);
  i8 = r594->size[0] * r594->size[1];
  r594->size[0] = 1;
  r594->size[1] = r518->size[1];
  emxEnsureCapacity((emxArray__common *)r594, i8, (int)sizeof(double));
  loop_ub = r518->size[0] * r518->size[1];
  emxFree_real_T(&r593);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r594->data[i8] = 0.0 * (r518->data[i8] - r522->data[i8]);
  }

  emxFree_real_T(&r522);
  emxInit_real_T(&r595, 2);
  rdivide(r594, 96487.0, r492);
  i8 = r595->size[0] * r595->size[1];
  r595->size[0] = 1;
  r595->size[1] = r520->size[1];
  emxEnsureCapacity((emxArray__common *)r595, i8, (int)sizeof(double));
  loop_ub = r520->size[0] * r520->size[1];
  emxFree_real_T(&r594);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r595->data[i8] = 0.0 * (r520->data[i8] - r527->data[i8]);
  }

  emxFree_real_T(&r527);
  emxInit_real_T(&r596, 2);
  rdivide(r595, 96487.0, r495);
  i8 = r596->size[0] * r596->size[1];
  r596->size[0] = 1;
  r596->size[1] = r525->size[1];
  emxEnsureCapacity((emxArray__common *)r596, i8, (int)sizeof(double));
  loop_ub = r525->size[0] * r525->size[1];
  emxFree_real_T(&r595);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r596->data[i8] = 0.0 * (r525->data[i8] - r532->data[i8]);
  }

  emxFree_real_T(&r525);
  emxFree_real_T(&r532);
  emxInit_real_T(&r597, 2);
  rdivide(r596, 96487.0, r497);
  i8 = r597->size[0] * r597->size[1];
  r597->size[0] = 1;
  r597->size[1] = r530->size[1];
  emxEnsureCapacity((emxArray__common *)r597, i8, (int)sizeof(double));
  loop_ub = r530->size[0] * r530->size[1];
  emxFree_real_T(&r596);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r597->data[i8] = 0.0 * (r530->data[i8] - r537->data[i8]);
  }

  emxFree_real_T(&r530);
  emxFree_real_T(&r537);
  emxInit_real_T(&r598, 2);
  rdivide(r597, 96487.0, r500);
  i8 = r598->size[0] * r598->size[1];
  r598->size[0] = 1;
  r598->size[1] = r535->size[1];
  emxEnsureCapacity((emxArray__common *)r598, i8, (int)sizeof(double));
  loop_ub = r535->size[0] * r535->size[1];
  emxFree_real_T(&r597);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r598->data[i8] = 0.0 * (r535->data[i8] - r542->data[i8]);
  }

  emxFree_real_T(&r535);
  emxFree_real_T(&r542);
  emxInit_real_T(&r599, 2);
  rdivide(r598, 96487.0, r502);
  i8 = r599->size[0] * r599->size[1];
  r599->size[0] = 1;
  r599->size[1] = r540->size[1];
  emxEnsureCapacity((emxArray__common *)r599, i8, (int)sizeof(double));
  loop_ub = r540->size[0] * r540->size[1];
  emxFree_real_T(&r598);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r599->data[i8] = 0.0 * (r540->data[i8] - r547->data[i8]);
  }

  emxFree_real_T(&r540);
  emxFree_real_T(&r547);
  emxInit_real_T(&r600, 2);
  rdivide(r599, 96487.0, r505);
  i8 = r600->size[0] * r600->size[1];
  r600->size[0] = 1;
  r600->size[1] = r545->size[1];
  emxEnsureCapacity((emxArray__common *)r600, i8, (int)sizeof(double));
  loop_ub = r545->size[0] * r545->size[1];
  emxFree_real_T(&r599);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r600->data[i8] = 0.0 * (r545->data[i8] - r552->data[i8]);
  }

  emxFree_real_T(&r545);
  emxFree_real_T(&r552);
  emxInit_real_T(&r601, 2);
  rdivide(r600, 96487.0, r507);
  i8 = r601->size[0] * r601->size[1];
  r601->size[0] = 1;
  r601->size[1] = r550->size[1];
  emxEnsureCapacity((emxArray__common *)r601, i8, (int)sizeof(double));
  loop_ub = r550->size[0] * r550->size[1];
  emxFree_real_T(&r600);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r601->data[i8] = 0.0 * (r550->data[i8] - r557->data[i8]);
  }

  emxFree_real_T(&r550);
  emxFree_real_T(&r557);
  emxInit_real_T(&r602, 2);
  rdivide(r601, 96487.0, r512);
  i8 = r602->size[0] * r602->size[1];
  r602->size[0] = 1;
  r602->size[1] = r555->size[1];
  emxEnsureCapacity((emxArray__common *)r602, i8, (int)sizeof(double));
  loop_ub = r555->size[0] * r555->size[1];
  emxFree_real_T(&r601);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r602->data[i8] = 0.0 * (r555->data[i8] - r562->data[i8]);
  }

  emxFree_real_T(&r555);
  emxFree_real_T(&r562);
  emxInit_real_T(&r603, 2);
  rdivide(r602, 96487.0, r516);
  i8 = r603->size[0] * r603->size[1];
  r603->size[0] = 1;
  r603->size[1] = r560->size[1];
  emxEnsureCapacity((emxArray__common *)r603, i8, (int)sizeof(double));
  loop_ub = r560->size[0] * r560->size[1];
  emxFree_real_T(&r602);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r603->data[i8] = 0.0 * (r560->data[i8] - r567->data[i8]);
  }

  emxFree_real_T(&r560);
  emxFree_real_T(&r567);
  emxInit_real_T(&r604, 2);
  rdivide(r603, 96487.0, r518);
  i8 = r604->size[0] * r604->size[1];
  r604->size[0] = 1;
  r604->size[1] = r565->size[1];
  emxEnsureCapacity((emxArray__common *)r604, i8, (int)sizeof(double));
  loop_ub = r565->size[0] * r565->size[1];
  emxFree_real_T(&r603);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r604->data[i8] = 0.0 * (r565->data[i8] - r572->data[i8]);
  }

  emxFree_real_T(&r565);
  emxFree_real_T(&r572);
  emxInit_real_T(&r605, 2);
  rdivide(r604, 96487.0, r520);
  i8 = r605->size[0] * r605->size[1];
  r605->size[0] = 1;
  r605->size[1] = r575->size[1];
  emxEnsureCapacity((emxArray__common *)r605, i8, (int)sizeof(double));
  loop_ub = r575->size[0] * r575->size[1];
  emxFree_real_T(&r604);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r605->data[i8] = (((((((((((((((((4.03 + r575->data[i8] * r510->data[i8]) +
      xSp->data[i8]) + r459->data[i8]) + r461->data[i8]) + r463->data[i8]) +
      i->data[i8]) + qdotDiffusionBSp->data[i8]) + qdotDiffusionBSn->data[i8]) +
      r470->data[i8]) + r472->data[i8]) + r475->data[i8]) + r477->data[i8]) +
                          r480->data[i8]) + r482->data[i8]) - ((((((((((((((0.01
      + r485->data[i8] * r570->data[i8]) + r487->data[i8]) + r490->data[i8]) +
      r492->data[i8]) + r495->data[i8]) + r497->data[i8]) + r500->data[i8]) +
      r502->data[i8]) + r505->data[i8]) + r507->data[i8]) + r512->data[i8]) +
      r516->data[i8]) + r518->data[i8]) + r520->data[i8])) - Vo->data[i8]) -
                      Vsn->data[i8]) - Vsp->data[i8];
  }

  emxFree_real_T(&r575);
  emxFree_real_T(&r570);
  emxFree_real_T(&r520);
  emxFree_real_T(&r510);
  emxFree_real_T(&r505);
  emxFree_real_T(&r500);
  emxFree_real_T(&r495);
  emxFree_real_T(&r490);
  emxFree_real_T(&r485);
  emxFree_real_T(&r480);
  emxFree_real_T(&r475);
  emxFree_real_T(&r470);
  emxFree_real_T(&r518);
  emxFree_real_T(&r516);
  emxFree_real_T(&r512);
  emxFree_real_T(&r507);
  emxFree_real_T(&r502);
  emxFree_real_T(&r497);
  emxFree_real_T(&r492);
  emxFree_real_T(&r487);
  emxFree_real_T(&r482);
  emxFree_real_T(&r477);
  emxFree_real_T(&r472);
  emxInit_real_T(&b_U, 2);
  loop_ub = U->size[1];
  i8 = b_U->size[0] * b_U->size[1];
  b_U->size[0] = 1;
  b_U->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_U, i8, (int)sizeof(double));
  for (i8 = 0; i8 < loop_ub; i8++) {
    b_U->data[b_U->size[0] * i8] = U->data[U->size[0] * i8];
  }

  emxInit_real_T(&r606, 2);
  b_rdivide(r605, b_U, i);

  /*  diffusion: */
  /* 	arrangement is qpS qpB qnB qnS. Current flows from neg to pos so right */
  /* 	to left. Diffusion direction by convention is positive going left to */
  /* 	right. */
  rdivide(qpB, 1.8E-5, r459);
  rdivide(qpS, 2.0000000000000003E-6, r461);
  i8 = r606->size[0] * r606->size[1];
  r606->size[0] = 1;
  r606->size[1] = r459->size[1];
  emxEnsureCapacity((emxArray__common *)r606, i8, (int)sizeof(double));
  loop_ub = r459->size[0] * r459->size[1];
  emxFree_real_T(&b_U);
  emxFree_real_T(&r605);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r606->data[i8] = r459->data[i8] - r461->data[i8];
  }

  emxInit_real_T(&r607, 2);
  rdivide(r606, 7.0E+6, qdotDiffusionBSp);
  rdivide(qnB, 1.8E-5, r459);
  rdivide(qnS, 2.0000000000000003E-6, r461);
  i8 = r607->size[0] * r607->size[1];
  r607->size[0] = 1;
  r607->size[1] = r459->size[1];
  emxEnsureCapacity((emxArray__common *)r607, i8, (int)sizeof(double));
  loop_ub = r459->size[0] * r459->size[1];
  emxFree_real_T(&r606);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r607->data[i8] = r459->data[i8] - r461->data[i8];
  }

  emxInit_real_T(&r608, 2);
  rdivide(r607, 7.0E+6, qdotDiffusionBSn);

  /*  charge */
  /*  ohmic drop */
  /*  surface overpotential (Butler-Volmer) */
  rdivide(qnS, 1266.666666666667, xpS);

  /*  mole fraction at neg electrode */
  rdivide(qpS, 11400.0, xSp);

  /*  mole fraction at pos electrode (assume same as bulk) */
  i8 = r608->size[0] * r608->size[1];
  r608->size[0] = 1;
  r608->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r608, i8, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r607);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r608->data[i8] = 1.0 - xpS->data[i8];
  }

  emxInit_real_T(&r609, 2);
  y_power(r608, b);
  y_power(xpS, r459);
  i8 = r609->size[0] * r609->size[1];
  r609->size[0] = 1;
  r609->size[1] = xSp->size[1];
  emxEnsureCapacity((emxArray__common *)r609, i8, (int)sizeof(double));
  loop_ub = xSp->size[0] * xSp->size[1];
  emxFree_real_T(&r608);
  emxFree_real_T(&xpS);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r609->data[i8] = 1.0 - xSp->data[i8];
  }

  emxInit_real_T(&r610, 2);
  y_power(r609, b_b);
  y_power(xSp, r461);
  rdivide(i, 0.000437545, r463);
  i8 = r610->size[0] * r610->size[1];
  r610->size[0] = 1;
  r610->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r610, i8, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r609);
  emxFree_real_T(&xSp);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r610->data[i8] = 2.0 * (2120.96 * b->data[i8] * r459->data[i8]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r611, 2);
  b_rdivide(r463, r610, r459);
  b_asinh(r459);
  rdivide(i, 0.00030962, r463);
  i8 = r611->size[0] * r611->size[1];
  r611->size[0] = 1;
  r611->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r611, i8, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r610);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r611->data[i8] = 2.0 * (248898.0 * b_b->data[i8] * r461->data[i8]);
  }

  emxFree_real_T(&b_b);
  b_rdivide(r463, r611, r461);
  b_asinh(r461);

  /*  transients */
  /*  temperature */
  /*  assuming constant for now */
  /*  update state */
  emxFree_real_T(&r611);
  for (i8 = 0; i8 < 2; i8++) {
    uv25[i8] = (unsigned int)X->size[i8];
  }

  i8 = XNew->size[0] * XNew->size[1];
  XNew->size[0] = (int)uv25[0];
  emxEnsureCapacity((emxArray__common *)XNew, i8, (int)sizeof(double));
  i8 = XNew->size[0] * XNew->size[1];
  XNew->size[1] = (int)uv25[1];
  emxEnsureCapacity((emxArray__common *)XNew, i8, (int)sizeof(double));
  loop_ub = (int)uv25[0] * (int)uv25[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[i8] = 0.0;
  }

  loop_ub = qpS->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[XNew->size[0] * i8] = qpS->data[qpS->size[0] * i8] + (i->data
      [i->size[0] * i8] + qdotDiffusionBSp->data[qdotDiffusionBSp->size[0] * i8]);
  }

  emxFree_real_T(&qpS);
  loop_ub = qpB->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[1 + XNew->size[0] * i8] = qpB->data[qpB->size[0] * i8] +
      ((-qdotDiffusionBSp->data[qdotDiffusionBSp->size[0] * i8] + i->data
        [i->size[0] * i8]) - i->data[i->size[0] * i8]);
  }

  emxFree_real_T(&qdotDiffusionBSp);
  emxFree_real_T(&qpB);
  loop_ub = qnB->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[2 + XNew->size[0] * i8] = qnB->data[qnB->size[0] * i8] +
      ((i->data[i->size[0] * i8] - i->data[i->size[0] * i8]) -
       qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * i8]);
  }

  emxFree_real_T(&qnB);
  loop_ub = qnS->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[3 + XNew->size[0] * i8] = qnS->data[qnS->size[0] * i8] +
      (qdotDiffusionBSn->data[qdotDiffusionBSn->size[0] * i8] - i->data[i->size
       [0] * i8]);
  }

  emxFree_real_T(&qdotDiffusionBSn);
  emxFree_real_T(&qnS);
  emxInit_real_T(&b_i, 2);
  i8 = b_i->size[0] * b_i->size[1];
  b_i->size[0] = 1;
  b_i->size[1] = i->size[1];
  emxEnsureCapacity((emxArray__common *)b_i, i8, (int)sizeof(double));
  loop_ub = i->size[0] * i->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    b_i->data[i8] = i->data[i8] * 0.117215 - Vo->data[i8];
  }

  rdivide(b_i, 6.08671, r463);
  loop_ub = Vo->size[1];
  emxFree_real_T(&b_i);
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[4 + XNew->size[0] * i8] = Vo->data[Vo->size[0] * i8] + r463->
      data[r463->size[0] * i8];
  }

  emxFree_real_T(&Vo);
  emxInit_real_T(&r612, 2);
  i8 = r612->size[0] * r612->size[1];
  r612->size[0] = 1;
  r612->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r612, i8, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    r612->data[i8] = 8.3144621 * Tb->data[i8];
  }

  emxInit_real_T(&c_i, 2);
  rdivide(r612, 96487.0, r463);
  rdivide(r463, 0.5, i);
  i8 = c_i->size[0] * c_i->size[1];
  c_i->size[0] = 1;
  c_i->size[1] = i->size[1];
  emxEnsureCapacity((emxArray__common *)c_i, i8, (int)sizeof(double));
  loop_ub = i->size[0] * i->size[1];
  emxFree_real_T(&r612);
  for (i8 = 0; i8 < loop_ub; i8++) {
    c_i->data[i8] = i->data[i8] * r459->data[i8] - Vsn->data[i8];
  }

  emxFree_real_T(&i);
  rdivide(c_i, 1001.38, r459);
  loop_ub = Vsn->size[1];
  emxFree_real_T(&c_i);
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[5 + XNew->size[0] * i8] = Vsn->data[Vsn->size[0] * i8] +
      r459->data[r459->size[0] * i8];
  }

  emxFree_real_T(&Vsn);
  emxInit_real_T(&r613, 2);
  i8 = r613->size[0] * r613->size[1];
  r613->size[0] = 1;
  r613->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r613, i8, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    r613->data[i8] = 8.3144621 * Tb->data[i8];
  }

  emxInit_real_T(&r614, 2);
  rdivide(r613, 96487.0, r459);
  rdivide(r459, 0.5, r463);
  i8 = r614->size[0] * r614->size[1];
  r614->size[0] = 1;
  r614->size[1] = r463->size[1];
  emxEnsureCapacity((emxArray__common *)r614, i8, (int)sizeof(double));
  loop_ub = r463->size[0] * r463->size[1];
  emxFree_real_T(&r613);
  for (i8 = 0; i8 < loop_ub; i8++) {
    r614->data[i8] = r463->data[i8] * r461->data[i8] - Vsp->data[i8];
  }

  emxFree_real_T(&r463);
  emxFree_real_T(&r461);
  rdivide(r614, 46.4311, r459);
  loop_ub = Vsp->size[1];
  emxFree_real_T(&r614);
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[6 + XNew->size[0] * i8] = Vsp->data[Vsp->size[0] * i8] +
      r459->data[r459->size[0] * i8];
  }

  emxFree_real_T(&r459);
  emxFree_real_T(&Vsp);
  loop_ub = Tb->size[1];
  for (i8 = 0; i8 < loop_ub; i8++) {
    XNew->data[7 + XNew->size[0] * i8] = Tb->data[Tb->size[0] * i8];
  }

  emxFree_real_T(&Tb);

  /*  add process noise */
}

/*
 * File trailer for StateEqnResistance.c
 *
 * [EOF]
 */
