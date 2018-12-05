/*
 * File: ThresholdEqnPower.c
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
#include "ThresholdEqnPower.h"
#include "BHM_emxutil.h"
#include "rdivide.h"
#include "log.h"
#include "power.h"
#include <stdio.h>

/* Function Definitions */

/*
 * determines if system is at EOL for given state
 *  it is vectorized, so X is nx by N, B is 1 by N
 * Arguments    : const emxArray_real_T *X
 *                emxArray_boolean_T *B
 * Return Type  : void
 */
void ThresholdEqnPower(const emxArray_real_T *X, emxArray_boolean_T *B)
{
  emxArray_real_T *Tb;
  int loop_ub;
  int i7;
  emxArray_real_T *b_X;
  emxArray_real_T *xpS;
  emxArray_real_T *r305;
  emxArray_real_T *b;
  emxArray_real_T *r306;
  emxArray_real_T *r307;
  emxArray_real_T *r308;
  emxArray_real_T *r309;
  emxArray_real_T *r310;
  emxArray_real_T *r311;
  emxArray_real_T *r312;
  emxArray_real_T *r313;
  emxArray_real_T *r314;
  emxArray_real_T *r315;
  emxArray_real_T *r316;
  emxArray_real_T *r317;
  emxArray_real_T *r318;
  emxArray_real_T *r319;
  emxArray_real_T *r320;
  emxArray_real_T *r321;
  emxArray_real_T *r322;
  emxArray_real_T *r323;
  emxArray_real_T *r324;
  emxArray_real_T *r325;
  emxArray_real_T *r326;
  emxArray_real_T *r327;
  emxArray_real_T *r328;
  emxArray_real_T *r329;
  emxArray_real_T *r330;
  emxArray_real_T *r331;
  emxArray_real_T *r332;
  emxArray_real_T *r333;
  emxArray_real_T *r334;
  emxArray_real_T *r335;
  emxArray_real_T *r336;
  emxArray_real_T *r337;
  emxArray_real_T *r338;
  emxArray_real_T *r339;
  emxArray_real_T *r340;
  emxArray_real_T *r341;
  emxArray_real_T *r342;
  emxArray_real_T *r343;
  emxArray_real_T *r344;
  emxArray_real_T *r345;
  emxArray_real_T *r346;
  emxArray_real_T *r347;
  emxArray_real_T *r348;
  emxArray_real_T *r349;
  emxArray_real_T *r350;
  emxArray_real_T *r351;
  emxArray_real_T *r352;
  emxArray_real_T *r353;
  emxArray_real_T *r354;
  emxArray_real_T *r355;
  emxArray_real_T *r356;
  emxArray_real_T *r357;
  emxArray_real_T *r358;
  emxArray_real_T *r359;
  emxArray_real_T *r360;
  emxArray_real_T *r361;
  emxArray_real_T *r362;
  emxArray_real_T *r363;
  emxArray_real_T *r364;
  emxArray_real_T *c_X;
  emxArray_real_T *xnS;
  emxArray_real_T *r365;
  emxArray_real_T *b_b;
  emxArray_real_T *r366;
  emxArray_real_T *r367;
  emxArray_real_T *r368;
  emxArray_real_T *r369;
  emxArray_real_T *r370;
  emxArray_real_T *r371;
  emxArray_real_T *r372;
  emxArray_real_T *r373;
  emxArray_real_T *r374;
  emxArray_real_T *r375;
  emxArray_real_T *r376;
  emxArray_real_T *r377;
  emxArray_real_T *r378;
  emxArray_real_T *r379;
  emxArray_real_T *r380;
  emxArray_real_T *r381;
  emxArray_real_T *r382;
  emxArray_real_T *r383;
  emxArray_real_T *r384;
  emxArray_real_T *r385;
  emxArray_real_T *r386;
  emxArray_real_T *r387;
  emxArray_real_T *r388;
  emxArray_real_T *r389;
  emxArray_real_T *r390;
  emxArray_real_T *r391;
  emxArray_real_T *r392;
  emxArray_real_T *r393;
  emxArray_real_T *r394;
  emxArray_real_T *r395;
  emxArray_real_T *r396;
  emxArray_real_T *r397;
  emxArray_real_T *r398;
  emxArray_real_T *r399;
  emxArray_real_T *r400;
  emxArray_real_T *r401;
  emxArray_real_T *r402;
  emxArray_real_T *r403;
  emxArray_real_T *r404;
  emxArray_real_T *r405;
  emxArray_real_T *r406;
  emxArray_real_T *r407;
  emxArray_real_T *r408;
  emxArray_real_T *r409;
  emxArray_real_T *r410;
  emxArray_real_T *r411;
  emxArray_real_T *r412;
  emxArray_real_T *r413;
  emxArray_real_T *r414;
  emxArray_real_T *r415;
  emxArray_real_T *r416;
  emxArray_real_T *r417;
  emxArray_real_T *r418;
  emxArray_real_T *r419;
  emxArray_real_T *r420;
  emxArray_real_T *r421;
  emxArray_real_T *r422;
  emxArray_real_T *r423;
  emxArray_real_T *r424;
  emxArray_real_T *r425;
  emxArray_real_T *r426;
  emxArray_real_T *r427;
  emxArray_real_T *r428;
  emxArray_real_T *r429;
  emxArray_real_T *r430;
  emxArray_real_T *r431;
  emxArray_real_T *r432;
  emxArray_real_T *r433;
  emxArray_real_T *r434;
  emxArray_real_T *r435;
  emxArray_real_T *r436;
  emxArray_real_T *r437;
  emxArray_real_T *r438;
  emxArray_real_T *r439;
  emxArray_real_T *r440;
  emxArray_real_T *r441;
  emxArray_real_T *r442;
  emxArray_real_T *r443;
  emxArray_real_T *r444;
  emxArray_real_T *r445;
  emxArray_real_T *r446;
  emxArray_real_T *r447;
  emxArray_real_T *r448;
  emxArray_real_T *r449;
  emxArray_real_T *r450;
  emxArray_real_T *r451;
  emxArray_real_T *r452;
  emxArray_real_T *r453;
  emxArray_real_T *r454;
  emxArray_real_T *r455;
  emxArray_real_T *r456;
  emxInit_real_T(&Tb, 2);

  /*  extract states */
  loop_ub = X->size[1];
  i7 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i7, (int)sizeof(double));
  for (i7 = 0; i7 < loop_ub; i7++) {
    Tb->data[Tb->size[0] * i7] = X->data[7 + X->size[0] * i7];
  }

  emxInit_real_T(&b_X, 2);

  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  loop_ub = X->size[1];
  i7 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i7, (int)sizeof(double));
  for (i7 = 0; i7 < loop_ub; i7++) {
    b_X->data[b_X->size[0] * i7] = X->data[X->size[0] * i7];
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r305, 2);
  rdivide(b_X, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i7 = r305->size[0] * r305->size[1];
  r305->size[0] = 1;
  r305->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r305, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&b_X);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r305->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r306, 2);
  power(r305, b);
  i7 = r306->size[0] * r306->size[1];
  r306->size[0] = 1;
  r306->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r306, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r305);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r306->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r307, 2);
  emxInit_real_T(&r308, 2);
  b_power(r306, r307);
  i7 = r308->size[0] * r308->size[1];
  r308->size[0] = 1;
  r308->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r308, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r306);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r308->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r309, 2);
  emxInit_real_T(&r310, 2);
  c_power(r308, r309);
  i7 = r310->size[0] * r310->size[1];
  r310->size[0] = 1;
  r310->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r310, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r308);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r310->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r311, 2);
  emxInit_real_T(&r312, 2);
  d_power(r310, r311);
  i7 = r312->size[0] * r312->size[1];
  r312->size[0] = 1;
  r312->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r312, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r310);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r312->data[i7] = 2.0 * xpS->data[i7] * 2.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r313, 2);
  emxInit_real_T(&r314, 2);
  b_rdivide(r312, r311, r313);
  i7 = r314->size[0] * r314->size[1];
  r314->size[0] = 1;
  r314->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r314, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r312);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r314->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r315, 2);
  e_power(r314, r311);
  i7 = r315->size[0] * r315->size[1];
  r315->size[0] = 1;
  r315->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r315, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r314);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r315->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r316, 2);
  emxInit_real_T(&r317, 2);
  f_power(r315, r316);
  i7 = r317->size[0] * r317->size[1];
  r317->size[0] = 1;
  r317->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r317, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r315);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r317->data[i7] = 2.0 * xpS->data[i7] * 3.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r318, 2);
  emxInit_real_T(&r319, 2);
  b_rdivide(r317, r316, r318);
  i7 = r319->size[0] * r319->size[1];
  r319->size[0] = 1;
  r319->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r319, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r317);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r319->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r320, 2);
  g_power(r319, r316);
  i7 = r320->size[0] * r320->size[1];
  r320->size[0] = 1;
  r320->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r320, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r319);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r320->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r321, 2);
  emxInit_real_T(&r322, 2);
  h_power(r320, r321);
  i7 = r322->size[0] * r322->size[1];
  r322->size[0] = 1;
  r322->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r322, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r320);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r322->data[i7] = 2.0 * xpS->data[i7] * 4.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r323, 2);
  emxInit_real_T(&r324, 2);
  b_rdivide(r322, r321, r323);
  i7 = r324->size[0] * r324->size[1];
  r324->size[0] = 1;
  r324->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r324, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r322);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r324->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r325, 2);
  i_power(r324, r321);
  i7 = r325->size[0] * r325->size[1];
  r325->size[0] = 1;
  r325->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r325, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r324);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r325->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r326, 2);
  emxInit_real_T(&r327, 2);
  j_power(r325, r326);
  i7 = r327->size[0] * r327->size[1];
  r327->size[0] = 1;
  r327->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r327, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r325);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r327->data[i7] = 2.0 * xpS->data[i7] * 5.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r328, 2);
  emxInit_real_T(&r329, 2);
  b_rdivide(r327, r326, r328);
  i7 = r329->size[0] * r329->size[1];
  r329->size[0] = 1;
  r329->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r329, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r327);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r329->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r330, 2);
  k_power(r329, r326);
  i7 = r330->size[0] * r330->size[1];
  r330->size[0] = 1;
  r330->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r330, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r329);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r330->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r331, 2);
  emxInit_real_T(&r332, 2);
  l_power(r330, r331);
  i7 = r332->size[0] * r332->size[1];
  r332->size[0] = 1;
  r332->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r332, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r330);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r332->data[i7] = 2.0 * xpS->data[i7] * 6.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r333, 2);
  emxInit_real_T(&r334, 2);
  b_rdivide(r332, r331, r333);
  i7 = r334->size[0] * r334->size[1];
  r334->size[0] = 1;
  r334->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r334, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r332);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r334->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r335, 2);
  m_power(r334, r331);
  i7 = r335->size[0] * r335->size[1];
  r335->size[0] = 1;
  r335->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r335, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r334);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r335->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r336, 2);
  emxInit_real_T(&r337, 2);
  n_power(r335, r336);
  i7 = r337->size[0] * r337->size[1];
  r337->size[0] = 1;
  r337->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r337, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r335);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r337->data[i7] = 2.0 * xpS->data[i7] * 7.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r338, 2);
  emxInit_real_T(&r339, 2);
  b_rdivide(r337, r336, r338);
  i7 = r339->size[0] * r339->size[1];
  r339->size[0] = 1;
  r339->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r339, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r337);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r339->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r340, 2);
  o_power(r339, r336);
  i7 = r340->size[0] * r340->size[1];
  r340->size[0] = 1;
  r340->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r340, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r339);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r340->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r341, 2);
  emxInit_real_T(&r342, 2);
  p_power(r340, r341);
  i7 = r342->size[0] * r342->size[1];
  r342->size[0] = 1;
  r342->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r342, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r340);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r342->data[i7] = 2.0 * xpS->data[i7] * 8.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r343, 2);
  emxInit_real_T(&r344, 2);
  b_rdivide(r342, r341, r343);
  i7 = r344->size[0] * r344->size[1];
  r344->size[0] = 1;
  r344->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r344, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r342);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r344->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r345, 2);
  q_power(r344, r341);
  i7 = r345->size[0] * r345->size[1];
  r345->size[0] = 1;
  r345->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r345, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r344);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r345->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r346, 2);
  emxInit_real_T(&r347, 2);
  r_power(r345, r346);
  i7 = r347->size[0] * r347->size[1];
  r347->size[0] = 1;
  r347->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r347, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r345);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r347->data[i7] = 2.0 * xpS->data[i7] * 9.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r348, 2);
  emxInit_real_T(&r349, 2);
  b_rdivide(r347, r346, r348);
  i7 = r349->size[0] * r349->size[1];
  r349->size[0] = 1;
  r349->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r349, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r347);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r349->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r350, 2);
  s_power(r349, r346);
  i7 = r350->size[0] * r350->size[1];
  r350->size[0] = 1;
  r350->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r350, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r349);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r350->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r351, 2);
  emxInit_real_T(&r352, 2);
  t_power(r350, r351);
  i7 = r352->size[0] * r352->size[1];
  r352->size[0] = 1;
  r352->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r352, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r350);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r352->data[i7] = 2.0 * xpS->data[i7] * 10.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r353, 2);
  emxInit_real_T(&r354, 2);
  b_rdivide(r352, r351, r353);
  i7 = r354->size[0] * r354->size[1];
  r354->size[0] = 1;
  r354->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r354, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r352);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r354->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r355, 2);
  u_power(r354, r351);
  i7 = r355->size[0] * r355->size[1];
  r355->size[0] = 1;
  r355->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r355, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r354);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r355->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r356, 2);
  emxInit_real_T(&r357, 2);
  v_power(r355, r356);
  i7 = r357->size[0] * r357->size[1];
  r357->size[0] = 1;
  r357->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r357, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r355);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r357->data[i7] = 2.0 * xpS->data[i7] * 11.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r358, 2);
  emxInit_real_T(&r359, 2);
  b_rdivide(r357, r356, r358);
  i7 = r359->size[0] * r359->size[1];
  r359->size[0] = 1;
  r359->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r359, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r357);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r359->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r360, 2);
  w_power(r359, r356);
  i7 = r360->size[0] * r360->size[1];
  r360->size[0] = 1;
  r360->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r360, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r359);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r360->data[i7] = 2.0 * xpS->data[i7] - 1.0;
  }

  emxInit_real_T(&r361, 2);
  emxInit_real_T(&r362, 2);
  x_power(r360, r361);
  i7 = r362->size[0] * r362->size[1];
  r362->size[0] = 1;
  r362->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r362, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r360);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r362->data[i7] = 2.0 * xpS->data[i7] * 12.0 * (1.0 - xpS->data[i7]);
  }

  emxInit_real_T(&r363, 2);
  emxInit_real_T(&r364, 2);
  b_rdivide(r362, r361, r363);
  i7 = r364->size[0] * r364->size[1];
  r364->size[0] = 1;
  r364->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r364, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r362);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r364->data[i7] = 1.0 - xpS->data[i7];
  }

  emxInit_real_T(&c_X, 2);
  b_rdivide(r364, xpS, r361);
  c_log(r361);

  /*  compute mole fraction at surface, negative electrode */
  loop_ub = X->size[1];
  i7 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i7, (int)sizeof(double));
  emxFree_real_T(&r364);
  for (i7 = 0; i7 < loop_ub; i7++) {
    c_X->data[c_X->size[0] * i7] = X->data[3 + X->size[0] * i7];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r365, 2);
  rdivide(c_X, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i7 = r365->size[0] * r365->size[1];
  r365->size[0] = 1;
  r365->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r365, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&c_X);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r365->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&b_b, 2);
  emxInit_real_T(&r366, 2);
  power(r365, b_b);
  i7 = r366->size[0] * r366->size[1];
  r366->size[0] = 1;
  r366->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r366, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r365);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r366->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r367, 2);
  emxInit_real_T(&r368, 2);
  b_power(r366, r367);
  i7 = r368->size[0] * r368->size[1];
  r368->size[0] = 1;
  r368->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r368, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r366);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r368->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r369, 2);
  emxInit_real_T(&r370, 2);
  c_power(r368, r369);
  i7 = r370->size[0] * r370->size[1];
  r370->size[0] = 1;
  r370->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r370, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r368);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r370->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r371, 2);
  emxInit_real_T(&r372, 2);
  d_power(r370, r371);
  i7 = r372->size[0] * r372->size[1];
  r372->size[0] = 1;
  r372->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r372, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r370);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r372->data[i7] = 2.0 * xnS->data[i7] * 2.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r373, 2);
  emxInit_real_T(&r374, 2);
  b_rdivide(r372, r371, r373);
  i7 = r374->size[0] * r374->size[1];
  r374->size[0] = 1;
  r374->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r374, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r372);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r374->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r375, 2);
  e_power(r374, r371);
  i7 = r375->size[0] * r375->size[1];
  r375->size[0] = 1;
  r375->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r375, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r374);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r375->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r376, 2);
  emxInit_real_T(&r377, 2);
  f_power(r375, r376);
  i7 = r377->size[0] * r377->size[1];
  r377->size[0] = 1;
  r377->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r377, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r375);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r377->data[i7] = 2.0 * xnS->data[i7] * 3.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r378, 2);
  emxInit_real_T(&r379, 2);
  b_rdivide(r377, r376, r378);
  i7 = r379->size[0] * r379->size[1];
  r379->size[0] = 1;
  r379->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r379, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r377);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r379->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r380, 2);
  g_power(r379, r376);
  i7 = r380->size[0] * r380->size[1];
  r380->size[0] = 1;
  r380->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r380, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r379);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r380->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r381, 2);
  emxInit_real_T(&r382, 2);
  h_power(r380, r381);
  i7 = r382->size[0] * r382->size[1];
  r382->size[0] = 1;
  r382->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r382, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r380);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r382->data[i7] = 2.0 * xnS->data[i7] * 4.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r383, 2);
  emxInit_real_T(&r384, 2);
  b_rdivide(r382, r381, r383);
  i7 = r384->size[0] * r384->size[1];
  r384->size[0] = 1;
  r384->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r384, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r382);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r384->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r385, 2);
  i_power(r384, r381);
  i7 = r385->size[0] * r385->size[1];
  r385->size[0] = 1;
  r385->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r385, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r384);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r385->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r386, 2);
  emxInit_real_T(&r387, 2);
  j_power(r385, r386);
  i7 = r387->size[0] * r387->size[1];
  r387->size[0] = 1;
  r387->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r387, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r385);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r387->data[i7] = 2.0 * xnS->data[i7] * 5.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r388, 2);
  emxInit_real_T(&r389, 2);
  b_rdivide(r387, r386, r388);
  i7 = r389->size[0] * r389->size[1];
  r389->size[0] = 1;
  r389->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r389, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r387);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r389->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r390, 2);
  k_power(r389, r386);
  i7 = r390->size[0] * r390->size[1];
  r390->size[0] = 1;
  r390->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r390, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r389);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r390->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r391, 2);
  emxInit_real_T(&r392, 2);
  l_power(r390, r391);
  i7 = r392->size[0] * r392->size[1];
  r392->size[0] = 1;
  r392->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r392, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r390);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r392->data[i7] = 2.0 * xnS->data[i7] * 6.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r393, 2);
  emxInit_real_T(&r394, 2);
  b_rdivide(r392, r391, r393);
  i7 = r394->size[0] * r394->size[1];
  r394->size[0] = 1;
  r394->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r394, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r392);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r394->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r395, 2);
  m_power(r394, r391);
  i7 = r395->size[0] * r395->size[1];
  r395->size[0] = 1;
  r395->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r395, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r394);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r395->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r396, 2);
  emxInit_real_T(&r397, 2);
  n_power(r395, r396);
  i7 = r397->size[0] * r397->size[1];
  r397->size[0] = 1;
  r397->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r397, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r395);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r397->data[i7] = 2.0 * xnS->data[i7] * 7.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r398, 2);
  emxInit_real_T(&r399, 2);
  b_rdivide(r397, r396, r398);
  i7 = r399->size[0] * r399->size[1];
  r399->size[0] = 1;
  r399->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r399, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r397);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r399->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r400, 2);
  o_power(r399, r396);
  i7 = r400->size[0] * r400->size[1];
  r400->size[0] = 1;
  r400->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r400, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r399);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r400->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r401, 2);
  emxInit_real_T(&r402, 2);
  p_power(r400, r401);
  i7 = r402->size[0] * r402->size[1];
  r402->size[0] = 1;
  r402->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r402, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r400);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r402->data[i7] = 2.0 * xnS->data[i7] * 8.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r403, 2);
  emxInit_real_T(&r404, 2);
  b_rdivide(r402, r401, r403);
  i7 = r404->size[0] * r404->size[1];
  r404->size[0] = 1;
  r404->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r404, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r402);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r404->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r405, 2);
  q_power(r404, r401);
  i7 = r405->size[0] * r405->size[1];
  r405->size[0] = 1;
  r405->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r405, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r404);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r405->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r406, 2);
  emxInit_real_T(&r407, 2);
  r_power(r405, r406);
  i7 = r407->size[0] * r407->size[1];
  r407->size[0] = 1;
  r407->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r407, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r405);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r407->data[i7] = 2.0 * xnS->data[i7] * 9.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r408, 2);
  emxInit_real_T(&r409, 2);
  b_rdivide(r407, r406, r408);
  i7 = r409->size[0] * r409->size[1];
  r409->size[0] = 1;
  r409->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r409, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r407);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r409->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r410, 2);
  s_power(r409, r406);
  i7 = r410->size[0] * r410->size[1];
  r410->size[0] = 1;
  r410->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r410, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r409);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r410->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r411, 2);
  emxInit_real_T(&r412, 2);
  t_power(r410, r411);
  i7 = r412->size[0] * r412->size[1];
  r412->size[0] = 1;
  r412->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r412, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r410);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r412->data[i7] = 2.0 * xnS->data[i7] * 10.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r413, 2);
  emxInit_real_T(&r414, 2);
  b_rdivide(r412, r411, r413);
  i7 = r414->size[0] * r414->size[1];
  r414->size[0] = 1;
  r414->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r414, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r412);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r414->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r415, 2);
  u_power(r414, r411);
  i7 = r415->size[0] * r415->size[1];
  r415->size[0] = 1;
  r415->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r415, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r414);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r415->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r416, 2);
  emxInit_real_T(&r417, 2);
  v_power(r415, r416);
  i7 = r417->size[0] * r417->size[1];
  r417->size[0] = 1;
  r417->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r417, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r415);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r417->data[i7] = 2.0 * xnS->data[i7] * 11.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r418, 2);
  emxInit_real_T(&r419, 2);
  b_rdivide(r417, r416, r418);
  i7 = r419->size[0] * r419->size[1];
  r419->size[0] = 1;
  r419->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r419, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r417);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r419->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r420, 2);
  w_power(r419, r416);
  i7 = r420->size[0] * r420->size[1];
  r420->size[0] = 1;
  r420->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r420, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r419);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r420->data[i7] = 2.0 * xnS->data[i7] - 1.0;
  }

  emxInit_real_T(&r421, 2);
  emxInit_real_T(&r422, 2);
  x_power(r420, r421);
  i7 = r422->size[0] * r422->size[1];
  r422->size[0] = 1;
  r422->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r422, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r420);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r422->data[i7] = 2.0 * xnS->data[i7] * 12.0 * (1.0 - xnS->data[i7]);
  }

  emxInit_real_T(&r423, 2);
  emxInit_real_T(&r424, 2);
  b_rdivide(r422, r421, r423);
  i7 = r424->size[0] * r424->size[1];
  r424->size[0] = 1;
  r424->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r424, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r422);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r424->data[i7] = 1.0 - xnS->data[i7];
  }

  emxInit_real_T(&r425, 2);
  b_rdivide(r424, xnS, r421);
  c_log(r421);

  /*  voltages */
  /*  individual performance constraints */
  /*  at EOL when any fail */
  i7 = r425->size[0] * r425->size[1];
  r425->size[0] = 1;
  r425->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r425, i7, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r424);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r425->data[i7] = 8.3144621 * Tb->data[i7];
  }

  emxInit_real_T(&r426, 2);
  emxInit_real_T(&r427, 2);
  rdivide(r425, 96487.0, r426);
  i7 = r427->size[0] * r427->size[1];
  r427->size[0] = 1;
  r427->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r427, i7, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r425);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r427->data[i7] = -31593.7 * b->data[i7];
  }

  emxInit_real_T(&r428, 2);
  emxInit_real_T(&r429, 2);
  rdivide(r427, 96487.0, r428);
  i7 = r429->size[0] * r429->size[1];
  r429->size[0] = 1;
  r429->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r429, i7, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r427);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r429->data[i7] = 2.0 * xpS->data[i7] * (1.0 - xpS->data[i7]);
  }

  emxFree_real_T(&xpS);
  emxInit_real_T(&r430, 2);
  rdivide(r429, 1.0, b);
  i7 = r430->size[0] * r430->size[1];
  r430->size[0] = 1;
  r430->size[1] = r307->size[1];
  emxEnsureCapacity((emxArray__common *)r430, i7, (int)sizeof(double));
  loop_ub = r307->size[0] * r307->size[1];
  emxFree_real_T(&r429);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r430->data[i7] = 0.106747 * (r307->data[i7] - b->data[i7]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r431, 2);
  rdivide(r430, 96487.0, r307);
  i7 = r431->size[0] * r431->size[1];
  r431->size[0] = 1;
  r431->size[1] = r309->size[1];
  emxEnsureCapacity((emxArray__common *)r431, i7, (int)sizeof(double));
  loop_ub = r309->size[0] * r309->size[1];
  emxFree_real_T(&r430);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r431->data[i7] = 24606.4 * (r309->data[i7] - r313->data[i7]);
  }

  emxInit_real_T(&r432, 2);
  rdivide(r431, 96487.0, r309);
  i7 = r432->size[0] * r432->size[1];
  r432->size[0] = 1;
  r432->size[1] = r311->size[1];
  emxEnsureCapacity((emxArray__common *)r432, i7, (int)sizeof(double));
  loop_ub = r311->size[0] * r311->size[1];
  emxFree_real_T(&r431);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r432->data[i7] = -78561.9 * (r311->data[i7] - r318->data[i7]);
  }

  emxInit_real_T(&r433, 2);
  rdivide(r432, 96487.0, r311);
  i7 = r433->size[0] * r433->size[1];
  r433->size[0] = 1;
  r433->size[1] = r316->size[1];
  emxEnsureCapacity((emxArray__common *)r433, i7, (int)sizeof(double));
  loop_ub = r316->size[0] * r316->size[1];
  emxFree_real_T(&r432);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r433->data[i7] = 13317.9 * (r316->data[i7] - r323->data[i7]);
  }

  emxInit_real_T(&r434, 2);
  rdivide(r433, 96487.0, r313);
  i7 = r434->size[0] * r434->size[1];
  r434->size[0] = 1;
  r434->size[1] = r321->size[1];
  emxEnsureCapacity((emxArray__common *)r434, i7, (int)sizeof(double));
  loop_ub = r321->size[0] * r321->size[1];
  emxFree_real_T(&r433);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r434->data[i7] = 307387.0 * (r321->data[i7] - r328->data[i7]);
  }

  emxInit_real_T(&r435, 2);
  rdivide(r434, 96487.0, r316);
  i7 = r435->size[0] * r435->size[1];
  r435->size[0] = 1;
  r435->size[1] = r326->size[1];
  emxEnsureCapacity((emxArray__common *)r435, i7, (int)sizeof(double));
  loop_ub = r326->size[0] * r326->size[1];
  emxFree_real_T(&r434);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r435->data[i7] = 84916.1 * (r326->data[i7] - r333->data[i7]);
  }

  emxInit_real_T(&r436, 2);
  rdivide(r435, 96487.0, r318);
  i7 = r436->size[0] * r436->size[1];
  r436->size[0] = 1;
  r436->size[1] = r331->size[1];
  emxEnsureCapacity((emxArray__common *)r436, i7, (int)sizeof(double));
  loop_ub = r331->size[0] * r331->size[1];
  emxFree_real_T(&r435);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r436->data[i7] = -1.07469E+6 * (r331->data[i7] - r338->data[i7]);
  }

  emxInit_real_T(&r437, 2);
  rdivide(r436, 96487.0, r321);
  i7 = r437->size[0] * r437->size[1];
  r437->size[0] = 1;
  r437->size[1] = r336->size[1];
  emxEnsureCapacity((emxArray__common *)r437, i7, (int)sizeof(double));
  loop_ub = r336->size[0] * r336->size[1];
  emxFree_real_T(&r436);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r437->data[i7] = 2285.04 * (r336->data[i7] - r343->data[i7]);
  }

  emxInit_real_T(&r438, 2);
  rdivide(r437, 96487.0, r323);
  i7 = r438->size[0] * r438->size[1];
  r438->size[0] = 1;
  r438->size[1] = r341->size[1];
  emxEnsureCapacity((emxArray__common *)r438, i7, (int)sizeof(double));
  loop_ub = r341->size[0] * r341->size[1];
  emxFree_real_T(&r437);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r438->data[i7] = 990894.0 * (r341->data[i7] - r348->data[i7]);
  }

  emxInit_real_T(&r439, 2);
  rdivide(r438, 96487.0, r326);
  i7 = r439->size[0] * r439->size[1];
  r439->size[0] = 1;
  r439->size[1] = r346->size[1];
  emxEnsureCapacity((emxArray__common *)r439, i7, (int)sizeof(double));
  loop_ub = r346->size[0] * r346->size[1];
  emxFree_real_T(&r438);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r439->data[i7] = 283920.0 * (r346->data[i7] - r353->data[i7]);
  }

  emxInit_real_T(&r440, 2);
  rdivide(r439, 96487.0, r328);
  i7 = r440->size[0] * r440->size[1];
  r440->size[0] = 1;
  r440->size[1] = r351->size[1];
  emxEnsureCapacity((emxArray__common *)r440, i7, (int)sizeof(double));
  loop_ub = r351->size[0] * r351->size[1];
  emxFree_real_T(&r439);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r440->data[i7] = -161513.0 * (r351->data[i7] - r358->data[i7]);
  }

  emxInit_real_T(&r441, 2);
  rdivide(r440, 96487.0, r331);
  i7 = r441->size[0] * r441->size[1];
  r441->size[0] = 1;
  r441->size[1] = r356->size[1];
  emxEnsureCapacity((emxArray__common *)r441, i7, (int)sizeof(double));
  loop_ub = r356->size[0] * r356->size[1];
  emxFree_real_T(&r440);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r441->data[i7] = -469218.0 * (r356->data[i7] - r363->data[i7]);
  }

  emxInit_real_T(&r442, 2);
  rdivide(r441, 96487.0, r333);
  i7 = r442->size[0] * r442->size[1];
  r442->size[0] = 1;
  r442->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r442, i7, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r441);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r442->data[i7] = 8.3144621 * Tb->data[i7];
  }

  emxFree_real_T(&Tb);
  emxInit_real_T(&r443, 2);
  rdivide(r442, 96487.0, r336);
  i7 = r443->size[0] * r443->size[1];
  r443->size[0] = 1;
  r443->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r443, i7, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r442);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r443->data[i7] = 86.19 * b_b->data[i7];
  }

  emxFree_real_T(&b_b);
  emxInit_real_T(&r444, 2);
  rdivide(r443, 96487.0, r338);
  i7 = r444->size[0] * r444->size[1];
  r444->size[0] = 1;
  r444->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r444, i7, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r443);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r444->data[i7] = 2.0 * xnS->data[i7] * (1.0 - xnS->data[i7]);
  }

  emxFree_real_T(&xnS);
  emxInit_real_T(&r445, 2);
  rdivide(r444, 1.0, r341);
  i7 = r445->size[0] * r445->size[1];
  r445->size[0] = 1;
  r445->size[1] = r367->size[1];
  emxEnsureCapacity((emxArray__common *)r445, i7, (int)sizeof(double));
  loop_ub = r367->size[0] * r367->size[1];
  emxFree_real_T(&r444);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r445->data[i7] = 0.0 * (r367->data[i7] - r341->data[i7]);
  }

  emxInit_real_T(&r446, 2);
  rdivide(r445, 96487.0, r341);
  i7 = r446->size[0] * r446->size[1];
  r446->size[0] = 1;
  r446->size[1] = r369->size[1];
  emxEnsureCapacity((emxArray__common *)r446, i7, (int)sizeof(double));
  loop_ub = r369->size[0] * r369->size[1];
  emxFree_real_T(&r445);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r446->data[i7] = 0.0 * (r369->data[i7] - r373->data[i7]);
  }

  emxFree_real_T(&r373);
  emxInit_real_T(&r447, 2);
  rdivide(r446, 96487.0, r343);
  i7 = r447->size[0] * r447->size[1];
  r447->size[0] = 1;
  r447->size[1] = r371->size[1];
  emxEnsureCapacity((emxArray__common *)r447, i7, (int)sizeof(double));
  loop_ub = r371->size[0] * r371->size[1];
  emxFree_real_T(&r446);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r447->data[i7] = 0.0 * (r371->data[i7] - r378->data[i7]);
  }

  emxFree_real_T(&r378);
  emxInit_real_T(&r448, 2);
  rdivide(r447, 96487.0, r346);
  i7 = r448->size[0] * r448->size[1];
  r448->size[0] = 1;
  r448->size[1] = r376->size[1];
  emxEnsureCapacity((emxArray__common *)r448, i7, (int)sizeof(double));
  loop_ub = r376->size[0] * r376->size[1];
  emxFree_real_T(&r447);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r448->data[i7] = 0.0 * (r376->data[i7] - r383->data[i7]);
  }

  emxFree_real_T(&r376);
  emxFree_real_T(&r383);
  emxInit_real_T(&r449, 2);
  rdivide(r448, 96487.0, r348);
  i7 = r449->size[0] * r449->size[1];
  r449->size[0] = 1;
  r449->size[1] = r381->size[1];
  emxEnsureCapacity((emxArray__common *)r449, i7, (int)sizeof(double));
  loop_ub = r381->size[0] * r381->size[1];
  emxFree_real_T(&r448);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r449->data[i7] = 0.0 * (r381->data[i7] - r388->data[i7]);
  }

  emxFree_real_T(&r381);
  emxFree_real_T(&r388);
  emxInit_real_T(&r450, 2);
  rdivide(r449, 96487.0, r351);
  i7 = r450->size[0] * r450->size[1];
  r450->size[0] = 1;
  r450->size[1] = r386->size[1];
  emxEnsureCapacity((emxArray__common *)r450, i7, (int)sizeof(double));
  loop_ub = r386->size[0] * r386->size[1];
  emxFree_real_T(&r449);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r450->data[i7] = 0.0 * (r386->data[i7] - r393->data[i7]);
  }

  emxFree_real_T(&r386);
  emxFree_real_T(&r393);
  emxInit_real_T(&r451, 2);
  rdivide(r450, 96487.0, r353);
  i7 = r451->size[0] * r451->size[1];
  r451->size[0] = 1;
  r451->size[1] = r391->size[1];
  emxEnsureCapacity((emxArray__common *)r451, i7, (int)sizeof(double));
  loop_ub = r391->size[0] * r391->size[1];
  emxFree_real_T(&r450);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r451->data[i7] = 0.0 * (r391->data[i7] - r398->data[i7]);
  }

  emxFree_real_T(&r391);
  emxFree_real_T(&r398);
  emxInit_real_T(&r452, 2);
  rdivide(r451, 96487.0, r356);
  i7 = r452->size[0] * r452->size[1];
  r452->size[0] = 1;
  r452->size[1] = r396->size[1];
  emxEnsureCapacity((emxArray__common *)r452, i7, (int)sizeof(double));
  loop_ub = r396->size[0] * r396->size[1];
  emxFree_real_T(&r451);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r452->data[i7] = 0.0 * (r396->data[i7] - r403->data[i7]);
  }

  emxFree_real_T(&r396);
  emxFree_real_T(&r403);
  emxInit_real_T(&r453, 2);
  rdivide(r452, 96487.0, r358);
  i7 = r453->size[0] * r453->size[1];
  r453->size[0] = 1;
  r453->size[1] = r401->size[1];
  emxEnsureCapacity((emxArray__common *)r453, i7, (int)sizeof(double));
  loop_ub = r401->size[0] * r401->size[1];
  emxFree_real_T(&r452);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r453->data[i7] = 0.0 * (r401->data[i7] - r408->data[i7]);
  }

  emxFree_real_T(&r401);
  emxFree_real_T(&r408);
  emxInit_real_T(&r454, 2);
  rdivide(r453, 96487.0, r363);
  i7 = r454->size[0] * r454->size[1];
  r454->size[0] = 1;
  r454->size[1] = r406->size[1];
  emxEnsureCapacity((emxArray__common *)r454, i7, (int)sizeof(double));
  loop_ub = r406->size[0] * r406->size[1];
  emxFree_real_T(&r453);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r454->data[i7] = 0.0 * (r406->data[i7] - r413->data[i7]);
  }

  emxFree_real_T(&r406);
  emxFree_real_T(&r413);
  emxInit_real_T(&r455, 2);
  rdivide(r454, 96487.0, r367);
  i7 = r455->size[0] * r455->size[1];
  r455->size[0] = 1;
  r455->size[1] = r411->size[1];
  emxEnsureCapacity((emxArray__common *)r455, i7, (int)sizeof(double));
  loop_ub = r411->size[0] * r411->size[1];
  emxFree_real_T(&r454);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r455->data[i7] = 0.0 * (r411->data[i7] - r418->data[i7]);
  }

  emxFree_real_T(&r411);
  emxFree_real_T(&r418);
  emxInit_real_T(&r456, 2);
  rdivide(r455, 96487.0, r369);
  i7 = r456->size[0] * r456->size[1];
  r456->size[0] = 1;
  r456->size[1] = r416->size[1];
  emxEnsureCapacity((emxArray__common *)r456, i7, (int)sizeof(double));
  loop_ub = r416->size[0] * r416->size[1];
  emxFree_real_T(&r455);
  for (i7 = 0; i7 < loop_ub; i7++) {
    r456->data[i7] = 0.0 * (r416->data[i7] - r423->data[i7]);
  }

  emxFree_real_T(&r416);
  emxFree_real_T(&r423);
  rdivide(r456, 96487.0, r371);
  i7 = B->size[0] * B->size[1];
  B->size[0] = 1;
  B->size[1] = r426->size[1];
  emxEnsureCapacity((emxArray__common *)B, i7, (int)sizeof(boolean_T));
  loop_ub = r426->size[1];
  emxFree_real_T(&r456);
  for (i7 = 0; i7 < loop_ub; i7++) {
    B->data[B->size[0] * i7] = !((((((((((((((((((4.03 + r426->data[r426->size[0]
      * i7] * r361->data[r361->size[0] * i7]) + r428->data[r428->size[0] * i7])
      + r307->data[r307->size[0] * i7]) + r309->data[r309->size[0] * i7]) +
      r311->data[r311->size[0] * i7]) + r313->data[r313->size[0] * i7]) +
      r316->data[r316->size[0] * i7]) + r318->data[r318->size[0] * i7]) +
      r321->data[r321->size[0] * i7]) + r323->data[r323->size[0] * i7]) +
      r326->data[r326->size[0] * i7]) + r328->data[r328->size[0] * i7]) +
      r331->data[r331->size[0] * i7]) + r333->data[r333->size[0] * i7]) -
                                    ((((((((((((((0.01 + r336->data[r336->size[0]
      * i7] * r421->data[r421->size[0] * i7]) + r338->data[r338->size[0] * i7])
      + r341->data[r341->size[0] * i7]) + r343->data[r343->size[0] * i7]) +
      r346->data[r346->size[0] * i7]) + r348->data[r348->size[0] * i7]) +
      r351->data[r351->size[0] * i7]) + r353->data[r353->size[0] * i7]) +
      r356->data[r356->size[0] * i7]) + r358->data[r358->size[0] * i7]) +
      r363->data[r363->size[0] * i7]) + r367->data[r367->size[0] * i7]) +
      r369->data[r369->size[0] * i7]) + r371->data[r371->size[0] * i7])) -
      X->data[4 + X->size[0] * i7]) - X->data[5 + X->size[0] * i7]) - X->data[6
      + X->size[0] * i7] > 2.5);
  }

  emxFree_real_T(&r428);
  emxFree_real_T(&r426);
  emxFree_real_T(&r421);
  emxFree_real_T(&r371);
  emxFree_real_T(&r361);
  emxFree_real_T(&r356);
  emxFree_real_T(&r351);
  emxFree_real_T(&r346);
  emxFree_real_T(&r341);
  emxFree_real_T(&r336);
  emxFree_real_T(&r331);
  emxFree_real_T(&r326);
  emxFree_real_T(&r321);
  emxFree_real_T(&r316);
  emxFree_real_T(&r311);
  emxFree_real_T(&r369);
  emxFree_real_T(&r367);
  emxFree_real_T(&r363);
  emxFree_real_T(&r358);
  emxFree_real_T(&r353);
  emxFree_real_T(&r348);
  emxFree_real_T(&r343);
  emxFree_real_T(&r338);
  emxFree_real_T(&r333);
  emxFree_real_T(&r328);
  emxFree_real_T(&r323);
  emxFree_real_T(&r318);
  emxFree_real_T(&r313);
  emxFree_real_T(&r309);
  emxFree_real_T(&r307);
}

/*
 * File trailer for ThresholdEqnPower.c
 *
 * [EOF]
 */
