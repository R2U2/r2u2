/*
 * File: ThresholdEqnCurrent.c
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
#include "ThresholdEqnCurrent.h"
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
void ThresholdEqnCurrent(const emxArray_real_T *X, emxArray_boolean_T *B)
{
  emxArray_real_T *Tb;
  int loop_ub;
  int i6;
  emxArray_real_T *b_X;
  emxArray_real_T *xpS;
  emxArray_real_T *r153;
  emxArray_real_T *b;
  emxArray_real_T *r154;
  emxArray_real_T *r155;
  emxArray_real_T *r156;
  emxArray_real_T *r157;
  emxArray_real_T *r158;
  emxArray_real_T *r159;
  emxArray_real_T *r160;
  emxArray_real_T *r161;
  emxArray_real_T *r162;
  emxArray_real_T *r163;
  emxArray_real_T *r164;
  emxArray_real_T *r165;
  emxArray_real_T *r166;
  emxArray_real_T *r167;
  emxArray_real_T *r168;
  emxArray_real_T *r169;
  emxArray_real_T *r170;
  emxArray_real_T *r171;
  emxArray_real_T *r172;
  emxArray_real_T *r173;
  emxArray_real_T *r174;
  emxArray_real_T *r175;
  emxArray_real_T *r176;
  emxArray_real_T *r177;
  emxArray_real_T *r178;
  emxArray_real_T *r179;
  emxArray_real_T *r180;
  emxArray_real_T *r181;
  emxArray_real_T *r182;
  emxArray_real_T *r183;
  emxArray_real_T *r184;
  emxArray_real_T *r185;
  emxArray_real_T *r186;
  emxArray_real_T *r187;
  emxArray_real_T *r188;
  emxArray_real_T *r189;
  emxArray_real_T *r190;
  emxArray_real_T *r191;
  emxArray_real_T *r192;
  emxArray_real_T *r193;
  emxArray_real_T *r194;
  emxArray_real_T *r195;
  emxArray_real_T *r196;
  emxArray_real_T *r197;
  emxArray_real_T *r198;
  emxArray_real_T *r199;
  emxArray_real_T *r200;
  emxArray_real_T *r201;
  emxArray_real_T *r202;
  emxArray_real_T *r203;
  emxArray_real_T *r204;
  emxArray_real_T *r205;
  emxArray_real_T *r206;
  emxArray_real_T *r207;
  emxArray_real_T *r208;
  emxArray_real_T *r209;
  emxArray_real_T *r210;
  emxArray_real_T *r211;
  emxArray_real_T *r212;
  emxArray_real_T *c_X;
  emxArray_real_T *xnS;
  emxArray_real_T *r213;
  emxArray_real_T *b_b;
  emxArray_real_T *r214;
  emxArray_real_T *r215;
  emxArray_real_T *r216;
  emxArray_real_T *r217;
  emxArray_real_T *r218;
  emxArray_real_T *r219;
  emxArray_real_T *r220;
  emxArray_real_T *r221;
  emxArray_real_T *r222;
  emxArray_real_T *r223;
  emxArray_real_T *r224;
  emxArray_real_T *r225;
  emxArray_real_T *r226;
  emxArray_real_T *r227;
  emxArray_real_T *r228;
  emxArray_real_T *r229;
  emxArray_real_T *r230;
  emxArray_real_T *r231;
  emxArray_real_T *r232;
  emxArray_real_T *r233;
  emxArray_real_T *r234;
  emxArray_real_T *r235;
  emxArray_real_T *r236;
  emxArray_real_T *r237;
  emxArray_real_T *r238;
  emxArray_real_T *r239;
  emxArray_real_T *r240;
  emxArray_real_T *r241;
  emxArray_real_T *r242;
  emxArray_real_T *r243;
  emxArray_real_T *r244;
  emxArray_real_T *r245;
  emxArray_real_T *r246;
  emxArray_real_T *r247;
  emxArray_real_T *r248;
  emxArray_real_T *r249;
  emxArray_real_T *r250;
  emxArray_real_T *r251;
  emxArray_real_T *r252;
  emxArray_real_T *r253;
  emxArray_real_T *r254;
  emxArray_real_T *r255;
  emxArray_real_T *r256;
  emxArray_real_T *r257;
  emxArray_real_T *r258;
  emxArray_real_T *r259;
  emxArray_real_T *r260;
  emxArray_real_T *r261;
  emxArray_real_T *r262;
  emxArray_real_T *r263;
  emxArray_real_T *r264;
  emxArray_real_T *r265;
  emxArray_real_T *r266;
  emxArray_real_T *r267;
  emxArray_real_T *r268;
  emxArray_real_T *r269;
  emxArray_real_T *r270;
  emxArray_real_T *r271;
  emxArray_real_T *r272;
  emxArray_real_T *r273;
  emxArray_real_T *r274;
  emxArray_real_T *r275;
  emxArray_real_T *r276;
  emxArray_real_T *r277;
  emxArray_real_T *r278;
  emxArray_real_T *r279;
  emxArray_real_T *r280;
  emxArray_real_T *r281;
  emxArray_real_T *r282;
  emxArray_real_T *r283;
  emxArray_real_T *r284;
  emxArray_real_T *r285;
  emxArray_real_T *r286;
  emxArray_real_T *r287;
  emxArray_real_T *r288;
  emxArray_real_T *r289;
  emxArray_real_T *r290;
  emxArray_real_T *r291;
  emxArray_real_T *r292;
  emxArray_real_T *r293;
  emxArray_real_T *r294;
  emxArray_real_T *r295;
  emxArray_real_T *r296;
  emxArray_real_T *r297;
  emxArray_real_T *r298;
  emxArray_real_T *r299;
  emxArray_real_T *r300;
  emxArray_real_T *r301;
  emxArray_real_T *r302;
  emxArray_real_T *r303;
  emxArray_real_T *r304;
  emxInit_real_T(&Tb, 2);

  /*  extract states */
  loop_ub = X->size[1];
  i6 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i6, (int)sizeof(double));
  for (i6 = 0; i6 < loop_ub; i6++) {
    Tb->data[Tb->size[0] * i6] = X->data[7 + X->size[0] * i6];
  }

  emxInit_real_T(&b_X, 2);

  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  loop_ub = X->size[1];
  i6 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i6, (int)sizeof(double));
  for (i6 = 0; i6 < loop_ub; i6++) {
    b_X->data[b_X->size[0] * i6] = X->data[X->size[0] * i6];
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r153, 2);
  rdivide(b_X, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i6 = r153->size[0] * r153->size[1];
  r153->size[0] = 1;
  r153->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r153, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&b_X);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r153->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r154, 2);
  power(r153, b);
  i6 = r154->size[0] * r154->size[1];
  r154->size[0] = 1;
  r154->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r154, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r153);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r154->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r155, 2);
  emxInit_real_T(&r156, 2);
  b_power(r154, r155);
  i6 = r156->size[0] * r156->size[1];
  r156->size[0] = 1;
  r156->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r156, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r154);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r156->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r157, 2);
  emxInit_real_T(&r158, 2);
  c_power(r156, r157);
  i6 = r158->size[0] * r158->size[1];
  r158->size[0] = 1;
  r158->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r158, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r156);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r158->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r159, 2);
  emxInit_real_T(&r160, 2);
  d_power(r158, r159);
  i6 = r160->size[0] * r160->size[1];
  r160->size[0] = 1;
  r160->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r160, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r158);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r160->data[i6] = 2.0 * xpS->data[i6] * 2.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r161, 2);
  emxInit_real_T(&r162, 2);
  b_rdivide(r160, r159, r161);
  i6 = r162->size[0] * r162->size[1];
  r162->size[0] = 1;
  r162->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r162, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r160);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r162->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r163, 2);
  e_power(r162, r159);
  i6 = r163->size[0] * r163->size[1];
  r163->size[0] = 1;
  r163->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r163, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r162);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r163->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r164, 2);
  emxInit_real_T(&r165, 2);
  f_power(r163, r164);
  i6 = r165->size[0] * r165->size[1];
  r165->size[0] = 1;
  r165->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r165, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r163);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r165->data[i6] = 2.0 * xpS->data[i6] * 3.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r166, 2);
  emxInit_real_T(&r167, 2);
  b_rdivide(r165, r164, r166);
  i6 = r167->size[0] * r167->size[1];
  r167->size[0] = 1;
  r167->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r167, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r165);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r167->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r168, 2);
  g_power(r167, r164);
  i6 = r168->size[0] * r168->size[1];
  r168->size[0] = 1;
  r168->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r168, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r167);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r168->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r169, 2);
  emxInit_real_T(&r170, 2);
  h_power(r168, r169);
  i6 = r170->size[0] * r170->size[1];
  r170->size[0] = 1;
  r170->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r170, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r168);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r170->data[i6] = 2.0 * xpS->data[i6] * 4.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r171, 2);
  emxInit_real_T(&r172, 2);
  b_rdivide(r170, r169, r171);
  i6 = r172->size[0] * r172->size[1];
  r172->size[0] = 1;
  r172->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r172, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r170);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r172->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r173, 2);
  i_power(r172, r169);
  i6 = r173->size[0] * r173->size[1];
  r173->size[0] = 1;
  r173->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r173, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r172);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r173->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r174, 2);
  emxInit_real_T(&r175, 2);
  j_power(r173, r174);
  i6 = r175->size[0] * r175->size[1];
  r175->size[0] = 1;
  r175->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r175, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r173);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r175->data[i6] = 2.0 * xpS->data[i6] * 5.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r176, 2);
  emxInit_real_T(&r177, 2);
  b_rdivide(r175, r174, r176);
  i6 = r177->size[0] * r177->size[1];
  r177->size[0] = 1;
  r177->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r177, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r175);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r177->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r178, 2);
  k_power(r177, r174);
  i6 = r178->size[0] * r178->size[1];
  r178->size[0] = 1;
  r178->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r178, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r177);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r178->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r179, 2);
  emxInit_real_T(&r180, 2);
  l_power(r178, r179);
  i6 = r180->size[0] * r180->size[1];
  r180->size[0] = 1;
  r180->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r180, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r178);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r180->data[i6] = 2.0 * xpS->data[i6] * 6.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r181, 2);
  emxInit_real_T(&r182, 2);
  b_rdivide(r180, r179, r181);
  i6 = r182->size[0] * r182->size[1];
  r182->size[0] = 1;
  r182->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r182, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r180);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r182->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r183, 2);
  m_power(r182, r179);
  i6 = r183->size[0] * r183->size[1];
  r183->size[0] = 1;
  r183->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r183, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r182);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r183->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r184, 2);
  emxInit_real_T(&r185, 2);
  n_power(r183, r184);
  i6 = r185->size[0] * r185->size[1];
  r185->size[0] = 1;
  r185->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r185, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r183);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r185->data[i6] = 2.0 * xpS->data[i6] * 7.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r186, 2);
  emxInit_real_T(&r187, 2);
  b_rdivide(r185, r184, r186);
  i6 = r187->size[0] * r187->size[1];
  r187->size[0] = 1;
  r187->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r187, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r185);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r187->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r188, 2);
  o_power(r187, r184);
  i6 = r188->size[0] * r188->size[1];
  r188->size[0] = 1;
  r188->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r188, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r187);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r188->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r189, 2);
  emxInit_real_T(&r190, 2);
  p_power(r188, r189);
  i6 = r190->size[0] * r190->size[1];
  r190->size[0] = 1;
  r190->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r190, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r188);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r190->data[i6] = 2.0 * xpS->data[i6] * 8.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r191, 2);
  emxInit_real_T(&r192, 2);
  b_rdivide(r190, r189, r191);
  i6 = r192->size[0] * r192->size[1];
  r192->size[0] = 1;
  r192->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r192, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r190);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r192->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r193, 2);
  q_power(r192, r189);
  i6 = r193->size[0] * r193->size[1];
  r193->size[0] = 1;
  r193->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r193, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r192);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r193->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r194, 2);
  emxInit_real_T(&r195, 2);
  r_power(r193, r194);
  i6 = r195->size[0] * r195->size[1];
  r195->size[0] = 1;
  r195->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r195, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r193);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r195->data[i6] = 2.0 * xpS->data[i6] * 9.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r196, 2);
  emxInit_real_T(&r197, 2);
  b_rdivide(r195, r194, r196);
  i6 = r197->size[0] * r197->size[1];
  r197->size[0] = 1;
  r197->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r197, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r195);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r197->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r198, 2);
  s_power(r197, r194);
  i6 = r198->size[0] * r198->size[1];
  r198->size[0] = 1;
  r198->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r198, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r197);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r198->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r199, 2);
  emxInit_real_T(&r200, 2);
  t_power(r198, r199);
  i6 = r200->size[0] * r200->size[1];
  r200->size[0] = 1;
  r200->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r200, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r198);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r200->data[i6] = 2.0 * xpS->data[i6] * 10.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r201, 2);
  emxInit_real_T(&r202, 2);
  b_rdivide(r200, r199, r201);
  i6 = r202->size[0] * r202->size[1];
  r202->size[0] = 1;
  r202->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r202, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r200);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r202->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r203, 2);
  u_power(r202, r199);
  i6 = r203->size[0] * r203->size[1];
  r203->size[0] = 1;
  r203->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r203, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r202);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r203->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r204, 2);
  emxInit_real_T(&r205, 2);
  v_power(r203, r204);
  i6 = r205->size[0] * r205->size[1];
  r205->size[0] = 1;
  r205->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r205, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r203);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r205->data[i6] = 2.0 * xpS->data[i6] * 11.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r206, 2);
  emxInit_real_T(&r207, 2);
  b_rdivide(r205, r204, r206);
  i6 = r207->size[0] * r207->size[1];
  r207->size[0] = 1;
  r207->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r207, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r205);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r207->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r208, 2);
  w_power(r207, r204);
  i6 = r208->size[0] * r208->size[1];
  r208->size[0] = 1;
  r208->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r208, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r207);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r208->data[i6] = 2.0 * xpS->data[i6] - 1.0;
  }

  emxInit_real_T(&r209, 2);
  emxInit_real_T(&r210, 2);
  x_power(r208, r209);
  i6 = r210->size[0] * r210->size[1];
  r210->size[0] = 1;
  r210->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r210, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r208);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r210->data[i6] = 2.0 * xpS->data[i6] * 12.0 * (1.0 - xpS->data[i6]);
  }

  emxInit_real_T(&r211, 2);
  emxInit_real_T(&r212, 2);
  b_rdivide(r210, r209, r211);
  i6 = r212->size[0] * r212->size[1];
  r212->size[0] = 1;
  r212->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r212, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r210);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r212->data[i6] = 1.0 - xpS->data[i6];
  }

  emxInit_real_T(&c_X, 2);
  b_rdivide(r212, xpS, r209);
  c_log(r209);

  /*  compute mole fraction at surface, negative electrode */
  loop_ub = X->size[1];
  i6 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i6, (int)sizeof(double));
  emxFree_real_T(&r212);
  for (i6 = 0; i6 < loop_ub; i6++) {
    c_X->data[c_X->size[0] * i6] = X->data[3 + X->size[0] * i6];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r213, 2);
  rdivide(c_X, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i6 = r213->size[0] * r213->size[1];
  r213->size[0] = 1;
  r213->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r213, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&c_X);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r213->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&b_b, 2);
  emxInit_real_T(&r214, 2);
  power(r213, b_b);
  i6 = r214->size[0] * r214->size[1];
  r214->size[0] = 1;
  r214->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r214, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r213);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r214->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r215, 2);
  emxInit_real_T(&r216, 2);
  b_power(r214, r215);
  i6 = r216->size[0] * r216->size[1];
  r216->size[0] = 1;
  r216->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r216, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r214);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r216->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r217, 2);
  emxInit_real_T(&r218, 2);
  c_power(r216, r217);
  i6 = r218->size[0] * r218->size[1];
  r218->size[0] = 1;
  r218->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r218, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r216);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r218->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r219, 2);
  emxInit_real_T(&r220, 2);
  d_power(r218, r219);
  i6 = r220->size[0] * r220->size[1];
  r220->size[0] = 1;
  r220->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r220, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r218);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r220->data[i6] = 2.0 * xnS->data[i6] * 2.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r221, 2);
  emxInit_real_T(&r222, 2);
  b_rdivide(r220, r219, r221);
  i6 = r222->size[0] * r222->size[1];
  r222->size[0] = 1;
  r222->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r222, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r220);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r222->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r223, 2);
  e_power(r222, r219);
  i6 = r223->size[0] * r223->size[1];
  r223->size[0] = 1;
  r223->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r223, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r222);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r223->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r224, 2);
  emxInit_real_T(&r225, 2);
  f_power(r223, r224);
  i6 = r225->size[0] * r225->size[1];
  r225->size[0] = 1;
  r225->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r225, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r223);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r225->data[i6] = 2.0 * xnS->data[i6] * 3.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r226, 2);
  emxInit_real_T(&r227, 2);
  b_rdivide(r225, r224, r226);
  i6 = r227->size[0] * r227->size[1];
  r227->size[0] = 1;
  r227->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r227, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r225);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r227->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r228, 2);
  g_power(r227, r224);
  i6 = r228->size[0] * r228->size[1];
  r228->size[0] = 1;
  r228->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r228, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r227);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r228->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r229, 2);
  emxInit_real_T(&r230, 2);
  h_power(r228, r229);
  i6 = r230->size[0] * r230->size[1];
  r230->size[0] = 1;
  r230->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r230, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r228);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r230->data[i6] = 2.0 * xnS->data[i6] * 4.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r231, 2);
  emxInit_real_T(&r232, 2);
  b_rdivide(r230, r229, r231);
  i6 = r232->size[0] * r232->size[1];
  r232->size[0] = 1;
  r232->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r232, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r230);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r232->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r233, 2);
  i_power(r232, r229);
  i6 = r233->size[0] * r233->size[1];
  r233->size[0] = 1;
  r233->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r233, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r232);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r233->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r234, 2);
  emxInit_real_T(&r235, 2);
  j_power(r233, r234);
  i6 = r235->size[0] * r235->size[1];
  r235->size[0] = 1;
  r235->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r235, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r233);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r235->data[i6] = 2.0 * xnS->data[i6] * 5.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r236, 2);
  emxInit_real_T(&r237, 2);
  b_rdivide(r235, r234, r236);
  i6 = r237->size[0] * r237->size[1];
  r237->size[0] = 1;
  r237->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r237, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r235);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r237->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r238, 2);
  k_power(r237, r234);
  i6 = r238->size[0] * r238->size[1];
  r238->size[0] = 1;
  r238->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r238, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r237);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r238->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r239, 2);
  emxInit_real_T(&r240, 2);
  l_power(r238, r239);
  i6 = r240->size[0] * r240->size[1];
  r240->size[0] = 1;
  r240->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r240, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r238);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r240->data[i6] = 2.0 * xnS->data[i6] * 6.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r241, 2);
  emxInit_real_T(&r242, 2);
  b_rdivide(r240, r239, r241);
  i6 = r242->size[0] * r242->size[1];
  r242->size[0] = 1;
  r242->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r242, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r240);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r242->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r243, 2);
  m_power(r242, r239);
  i6 = r243->size[0] * r243->size[1];
  r243->size[0] = 1;
  r243->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r243, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r242);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r243->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r244, 2);
  emxInit_real_T(&r245, 2);
  n_power(r243, r244);
  i6 = r245->size[0] * r245->size[1];
  r245->size[0] = 1;
  r245->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r245, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r243);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r245->data[i6] = 2.0 * xnS->data[i6] * 7.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r246, 2);
  emxInit_real_T(&r247, 2);
  b_rdivide(r245, r244, r246);
  i6 = r247->size[0] * r247->size[1];
  r247->size[0] = 1;
  r247->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r247, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r245);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r247->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r248, 2);
  o_power(r247, r244);
  i6 = r248->size[0] * r248->size[1];
  r248->size[0] = 1;
  r248->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r248, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r247);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r248->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r249, 2);
  emxInit_real_T(&r250, 2);
  p_power(r248, r249);
  i6 = r250->size[0] * r250->size[1];
  r250->size[0] = 1;
  r250->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r250, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r248);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r250->data[i6] = 2.0 * xnS->data[i6] * 8.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r251, 2);
  emxInit_real_T(&r252, 2);
  b_rdivide(r250, r249, r251);
  i6 = r252->size[0] * r252->size[1];
  r252->size[0] = 1;
  r252->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r252, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r250);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r252->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r253, 2);
  q_power(r252, r249);
  i6 = r253->size[0] * r253->size[1];
  r253->size[0] = 1;
  r253->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r253, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r252);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r253->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r254, 2);
  emxInit_real_T(&r255, 2);
  r_power(r253, r254);
  i6 = r255->size[0] * r255->size[1];
  r255->size[0] = 1;
  r255->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r255, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r253);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r255->data[i6] = 2.0 * xnS->data[i6] * 9.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r256, 2);
  emxInit_real_T(&r257, 2);
  b_rdivide(r255, r254, r256);
  i6 = r257->size[0] * r257->size[1];
  r257->size[0] = 1;
  r257->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r257, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r255);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r257->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r258, 2);
  s_power(r257, r254);
  i6 = r258->size[0] * r258->size[1];
  r258->size[0] = 1;
  r258->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r258, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r257);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r258->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r259, 2);
  emxInit_real_T(&r260, 2);
  t_power(r258, r259);
  i6 = r260->size[0] * r260->size[1];
  r260->size[0] = 1;
  r260->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r260, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r258);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r260->data[i6] = 2.0 * xnS->data[i6] * 10.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r261, 2);
  emxInit_real_T(&r262, 2);
  b_rdivide(r260, r259, r261);
  i6 = r262->size[0] * r262->size[1];
  r262->size[0] = 1;
  r262->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r262, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r260);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r262->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r263, 2);
  u_power(r262, r259);
  i6 = r263->size[0] * r263->size[1];
  r263->size[0] = 1;
  r263->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r263, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r262);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r263->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r264, 2);
  emxInit_real_T(&r265, 2);
  v_power(r263, r264);
  i6 = r265->size[0] * r265->size[1];
  r265->size[0] = 1;
  r265->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r265, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r263);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r265->data[i6] = 2.0 * xnS->data[i6] * 11.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r266, 2);
  emxInit_real_T(&r267, 2);
  b_rdivide(r265, r264, r266);
  i6 = r267->size[0] * r267->size[1];
  r267->size[0] = 1;
  r267->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r267, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r265);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r267->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r268, 2);
  w_power(r267, r264);
  i6 = r268->size[0] * r268->size[1];
  r268->size[0] = 1;
  r268->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r268, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r267);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r268->data[i6] = 2.0 * xnS->data[i6] - 1.0;
  }

  emxInit_real_T(&r269, 2);
  emxInit_real_T(&r270, 2);
  x_power(r268, r269);
  i6 = r270->size[0] * r270->size[1];
  r270->size[0] = 1;
  r270->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r270, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r268);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r270->data[i6] = 2.0 * xnS->data[i6] * 12.0 * (1.0 - xnS->data[i6]);
  }

  emxInit_real_T(&r271, 2);
  emxInit_real_T(&r272, 2);
  b_rdivide(r270, r269, r271);
  i6 = r272->size[0] * r272->size[1];
  r272->size[0] = 1;
  r272->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r272, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r270);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r272->data[i6] = 1.0 - xnS->data[i6];
  }

  emxInit_real_T(&r273, 2);
  b_rdivide(r272, xnS, r269);
  c_log(r269);

  /*  voltages */
  /*  individual performance constraints */
  /*  at EOL when any fail */
  i6 = r273->size[0] * r273->size[1];
  r273->size[0] = 1;
  r273->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r273, i6, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r272);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r273->data[i6] = 8.3144621 * Tb->data[i6];
  }

  emxInit_real_T(&r274, 2);
  emxInit_real_T(&r275, 2);
  rdivide(r273, 96487.0, r274);
  i6 = r275->size[0] * r275->size[1];
  r275->size[0] = 1;
  r275->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r275, i6, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r273);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r275->data[i6] = -31593.7 * b->data[i6];
  }

  emxInit_real_T(&r276, 2);
  emxInit_real_T(&r277, 2);
  rdivide(r275, 96487.0, r276);
  i6 = r277->size[0] * r277->size[1];
  r277->size[0] = 1;
  r277->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r277, i6, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r275);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r277->data[i6] = 2.0 * xpS->data[i6] * (1.0 - xpS->data[i6]);
  }

  emxFree_real_T(&xpS);
  emxInit_real_T(&r278, 2);
  rdivide(r277, 1.0, b);
  i6 = r278->size[0] * r278->size[1];
  r278->size[0] = 1;
  r278->size[1] = r155->size[1];
  emxEnsureCapacity((emxArray__common *)r278, i6, (int)sizeof(double));
  loop_ub = r155->size[0] * r155->size[1];
  emxFree_real_T(&r277);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r278->data[i6] = 0.106747 * (r155->data[i6] - b->data[i6]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r279, 2);
  rdivide(r278, 96487.0, r155);
  i6 = r279->size[0] * r279->size[1];
  r279->size[0] = 1;
  r279->size[1] = r157->size[1];
  emxEnsureCapacity((emxArray__common *)r279, i6, (int)sizeof(double));
  loop_ub = r157->size[0] * r157->size[1];
  emxFree_real_T(&r278);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r279->data[i6] = 24606.4 * (r157->data[i6] - r161->data[i6]);
  }

  emxInit_real_T(&r280, 2);
  rdivide(r279, 96487.0, r157);
  i6 = r280->size[0] * r280->size[1];
  r280->size[0] = 1;
  r280->size[1] = r159->size[1];
  emxEnsureCapacity((emxArray__common *)r280, i6, (int)sizeof(double));
  loop_ub = r159->size[0] * r159->size[1];
  emxFree_real_T(&r279);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r280->data[i6] = -78561.9 * (r159->data[i6] - r166->data[i6]);
  }

  emxInit_real_T(&r281, 2);
  rdivide(r280, 96487.0, r159);
  i6 = r281->size[0] * r281->size[1];
  r281->size[0] = 1;
  r281->size[1] = r164->size[1];
  emxEnsureCapacity((emxArray__common *)r281, i6, (int)sizeof(double));
  loop_ub = r164->size[0] * r164->size[1];
  emxFree_real_T(&r280);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r281->data[i6] = 13317.9 * (r164->data[i6] - r171->data[i6]);
  }

  emxInit_real_T(&r282, 2);
  rdivide(r281, 96487.0, r161);
  i6 = r282->size[0] * r282->size[1];
  r282->size[0] = 1;
  r282->size[1] = r169->size[1];
  emxEnsureCapacity((emxArray__common *)r282, i6, (int)sizeof(double));
  loop_ub = r169->size[0] * r169->size[1];
  emxFree_real_T(&r281);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r282->data[i6] = 307387.0 * (r169->data[i6] - r176->data[i6]);
  }

  emxInit_real_T(&r283, 2);
  rdivide(r282, 96487.0, r164);
  i6 = r283->size[0] * r283->size[1];
  r283->size[0] = 1;
  r283->size[1] = r174->size[1];
  emxEnsureCapacity((emxArray__common *)r283, i6, (int)sizeof(double));
  loop_ub = r174->size[0] * r174->size[1];
  emxFree_real_T(&r282);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r283->data[i6] = 84916.1 * (r174->data[i6] - r181->data[i6]);
  }

  emxInit_real_T(&r284, 2);
  rdivide(r283, 96487.0, r166);
  i6 = r284->size[0] * r284->size[1];
  r284->size[0] = 1;
  r284->size[1] = r179->size[1];
  emxEnsureCapacity((emxArray__common *)r284, i6, (int)sizeof(double));
  loop_ub = r179->size[0] * r179->size[1];
  emxFree_real_T(&r283);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r284->data[i6] = -1.07469E+6 * (r179->data[i6] - r186->data[i6]);
  }

  emxInit_real_T(&r285, 2);
  rdivide(r284, 96487.0, r169);
  i6 = r285->size[0] * r285->size[1];
  r285->size[0] = 1;
  r285->size[1] = r184->size[1];
  emxEnsureCapacity((emxArray__common *)r285, i6, (int)sizeof(double));
  loop_ub = r184->size[0] * r184->size[1];
  emxFree_real_T(&r284);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r285->data[i6] = 2285.04 * (r184->data[i6] - r191->data[i6]);
  }

  emxInit_real_T(&r286, 2);
  rdivide(r285, 96487.0, r171);
  i6 = r286->size[0] * r286->size[1];
  r286->size[0] = 1;
  r286->size[1] = r189->size[1];
  emxEnsureCapacity((emxArray__common *)r286, i6, (int)sizeof(double));
  loop_ub = r189->size[0] * r189->size[1];
  emxFree_real_T(&r285);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r286->data[i6] = 990894.0 * (r189->data[i6] - r196->data[i6]);
  }

  emxInit_real_T(&r287, 2);
  rdivide(r286, 96487.0, r174);
  i6 = r287->size[0] * r287->size[1];
  r287->size[0] = 1;
  r287->size[1] = r194->size[1];
  emxEnsureCapacity((emxArray__common *)r287, i6, (int)sizeof(double));
  loop_ub = r194->size[0] * r194->size[1];
  emxFree_real_T(&r286);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r287->data[i6] = 283920.0 * (r194->data[i6] - r201->data[i6]);
  }

  emxInit_real_T(&r288, 2);
  rdivide(r287, 96487.0, r176);
  i6 = r288->size[0] * r288->size[1];
  r288->size[0] = 1;
  r288->size[1] = r199->size[1];
  emxEnsureCapacity((emxArray__common *)r288, i6, (int)sizeof(double));
  loop_ub = r199->size[0] * r199->size[1];
  emxFree_real_T(&r287);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r288->data[i6] = -161513.0 * (r199->data[i6] - r206->data[i6]);
  }

  emxInit_real_T(&r289, 2);
  rdivide(r288, 96487.0, r179);
  i6 = r289->size[0] * r289->size[1];
  r289->size[0] = 1;
  r289->size[1] = r204->size[1];
  emxEnsureCapacity((emxArray__common *)r289, i6, (int)sizeof(double));
  loop_ub = r204->size[0] * r204->size[1];
  emxFree_real_T(&r288);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r289->data[i6] = -469218.0 * (r204->data[i6] - r211->data[i6]);
  }

  emxInit_real_T(&r290, 2);
  rdivide(r289, 96487.0, r181);
  i6 = r290->size[0] * r290->size[1];
  r290->size[0] = 1;
  r290->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r290, i6, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r289);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r290->data[i6] = 8.3144621 * Tb->data[i6];
  }

  emxFree_real_T(&Tb);
  emxInit_real_T(&r291, 2);
  rdivide(r290, 96487.0, r184);
  i6 = r291->size[0] * r291->size[1];
  r291->size[0] = 1;
  r291->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r291, i6, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r290);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r291->data[i6] = 86.19 * b_b->data[i6];
  }

  emxFree_real_T(&b_b);
  emxInit_real_T(&r292, 2);
  rdivide(r291, 96487.0, r186);
  i6 = r292->size[0] * r292->size[1];
  r292->size[0] = 1;
  r292->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r292, i6, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r291);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r292->data[i6] = 2.0 * xnS->data[i6] * (1.0 - xnS->data[i6]);
  }

  emxFree_real_T(&xnS);
  emxInit_real_T(&r293, 2);
  rdivide(r292, 1.0, r189);
  i6 = r293->size[0] * r293->size[1];
  r293->size[0] = 1;
  r293->size[1] = r215->size[1];
  emxEnsureCapacity((emxArray__common *)r293, i6, (int)sizeof(double));
  loop_ub = r215->size[0] * r215->size[1];
  emxFree_real_T(&r292);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r293->data[i6] = 0.0 * (r215->data[i6] - r189->data[i6]);
  }

  emxInit_real_T(&r294, 2);
  rdivide(r293, 96487.0, r189);
  i6 = r294->size[0] * r294->size[1];
  r294->size[0] = 1;
  r294->size[1] = r217->size[1];
  emxEnsureCapacity((emxArray__common *)r294, i6, (int)sizeof(double));
  loop_ub = r217->size[0] * r217->size[1];
  emxFree_real_T(&r293);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r294->data[i6] = 0.0 * (r217->data[i6] - r221->data[i6]);
  }

  emxFree_real_T(&r221);
  emxInit_real_T(&r295, 2);
  rdivide(r294, 96487.0, r191);
  i6 = r295->size[0] * r295->size[1];
  r295->size[0] = 1;
  r295->size[1] = r219->size[1];
  emxEnsureCapacity((emxArray__common *)r295, i6, (int)sizeof(double));
  loop_ub = r219->size[0] * r219->size[1];
  emxFree_real_T(&r294);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r295->data[i6] = 0.0 * (r219->data[i6] - r226->data[i6]);
  }

  emxFree_real_T(&r226);
  emxInit_real_T(&r296, 2);
  rdivide(r295, 96487.0, r194);
  i6 = r296->size[0] * r296->size[1];
  r296->size[0] = 1;
  r296->size[1] = r224->size[1];
  emxEnsureCapacity((emxArray__common *)r296, i6, (int)sizeof(double));
  loop_ub = r224->size[0] * r224->size[1];
  emxFree_real_T(&r295);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r296->data[i6] = 0.0 * (r224->data[i6] - r231->data[i6]);
  }

  emxFree_real_T(&r224);
  emxFree_real_T(&r231);
  emxInit_real_T(&r297, 2);
  rdivide(r296, 96487.0, r196);
  i6 = r297->size[0] * r297->size[1];
  r297->size[0] = 1;
  r297->size[1] = r229->size[1];
  emxEnsureCapacity((emxArray__common *)r297, i6, (int)sizeof(double));
  loop_ub = r229->size[0] * r229->size[1];
  emxFree_real_T(&r296);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r297->data[i6] = 0.0 * (r229->data[i6] - r236->data[i6]);
  }

  emxFree_real_T(&r229);
  emxFree_real_T(&r236);
  emxInit_real_T(&r298, 2);
  rdivide(r297, 96487.0, r199);
  i6 = r298->size[0] * r298->size[1];
  r298->size[0] = 1;
  r298->size[1] = r234->size[1];
  emxEnsureCapacity((emxArray__common *)r298, i6, (int)sizeof(double));
  loop_ub = r234->size[0] * r234->size[1];
  emxFree_real_T(&r297);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r298->data[i6] = 0.0 * (r234->data[i6] - r241->data[i6]);
  }

  emxFree_real_T(&r234);
  emxFree_real_T(&r241);
  emxInit_real_T(&r299, 2);
  rdivide(r298, 96487.0, r201);
  i6 = r299->size[0] * r299->size[1];
  r299->size[0] = 1;
  r299->size[1] = r239->size[1];
  emxEnsureCapacity((emxArray__common *)r299, i6, (int)sizeof(double));
  loop_ub = r239->size[0] * r239->size[1];
  emxFree_real_T(&r298);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r299->data[i6] = 0.0 * (r239->data[i6] - r246->data[i6]);
  }

  emxFree_real_T(&r239);
  emxFree_real_T(&r246);
  emxInit_real_T(&r300, 2);
  rdivide(r299, 96487.0, r204);
  i6 = r300->size[0] * r300->size[1];
  r300->size[0] = 1;
  r300->size[1] = r244->size[1];
  emxEnsureCapacity((emxArray__common *)r300, i6, (int)sizeof(double));
  loop_ub = r244->size[0] * r244->size[1];
  emxFree_real_T(&r299);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r300->data[i6] = 0.0 * (r244->data[i6] - r251->data[i6]);
  }

  emxFree_real_T(&r244);
  emxFree_real_T(&r251);
  emxInit_real_T(&r301, 2);
  rdivide(r300, 96487.0, r206);
  i6 = r301->size[0] * r301->size[1];
  r301->size[0] = 1;
  r301->size[1] = r249->size[1];
  emxEnsureCapacity((emxArray__common *)r301, i6, (int)sizeof(double));
  loop_ub = r249->size[0] * r249->size[1];
  emxFree_real_T(&r300);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r301->data[i6] = 0.0 * (r249->data[i6] - r256->data[i6]);
  }

  emxFree_real_T(&r249);
  emxFree_real_T(&r256);
  emxInit_real_T(&r302, 2);
  rdivide(r301, 96487.0, r211);
  i6 = r302->size[0] * r302->size[1];
  r302->size[0] = 1;
  r302->size[1] = r254->size[1];
  emxEnsureCapacity((emxArray__common *)r302, i6, (int)sizeof(double));
  loop_ub = r254->size[0] * r254->size[1];
  emxFree_real_T(&r301);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r302->data[i6] = 0.0 * (r254->data[i6] - r261->data[i6]);
  }

  emxFree_real_T(&r254);
  emxFree_real_T(&r261);
  emxInit_real_T(&r303, 2);
  rdivide(r302, 96487.0, r215);
  i6 = r303->size[0] * r303->size[1];
  r303->size[0] = 1;
  r303->size[1] = r259->size[1];
  emxEnsureCapacity((emxArray__common *)r303, i6, (int)sizeof(double));
  loop_ub = r259->size[0] * r259->size[1];
  emxFree_real_T(&r302);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r303->data[i6] = 0.0 * (r259->data[i6] - r266->data[i6]);
  }

  emxFree_real_T(&r259);
  emxFree_real_T(&r266);
  emxInit_real_T(&r304, 2);
  rdivide(r303, 96487.0, r217);
  i6 = r304->size[0] * r304->size[1];
  r304->size[0] = 1;
  r304->size[1] = r264->size[1];
  emxEnsureCapacity((emxArray__common *)r304, i6, (int)sizeof(double));
  loop_ub = r264->size[0] * r264->size[1];
  emxFree_real_T(&r303);
  for (i6 = 0; i6 < loop_ub; i6++) {
    r304->data[i6] = 0.0 * (r264->data[i6] - r271->data[i6]);
  }

  emxFree_real_T(&r264);
  emxFree_real_T(&r271);
  rdivide(r304, 96487.0, r219);
  i6 = B->size[0] * B->size[1];
  B->size[0] = 1;
  B->size[1] = r274->size[1];
  emxEnsureCapacity((emxArray__common *)B, i6, (int)sizeof(boolean_T));
  loop_ub = r274->size[1];
  emxFree_real_T(&r304);
  for (i6 = 0; i6 < loop_ub; i6++) {
    B->data[B->size[0] * i6] = !((((((((((((((((((4.03 + r274->data[r274->size[0]
      * i6] * r209->data[r209->size[0] * i6]) + r276->data[r276->size[0] * i6])
      + r155->data[r155->size[0] * i6]) + r157->data[r157->size[0] * i6]) +
      r159->data[r159->size[0] * i6]) + r161->data[r161->size[0] * i6]) +
      r164->data[r164->size[0] * i6]) + r166->data[r166->size[0] * i6]) +
      r169->data[r169->size[0] * i6]) + r171->data[r171->size[0] * i6]) +
      r174->data[r174->size[0] * i6]) + r176->data[r176->size[0] * i6]) +
      r179->data[r179->size[0] * i6]) + r181->data[r181->size[0] * i6]) -
                                    ((((((((((((((0.01 + r184->data[r184->size[0]
      * i6] * r269->data[r269->size[0] * i6]) + r186->data[r186->size[0] * i6])
      + r189->data[r189->size[0] * i6]) + r191->data[r191->size[0] * i6]) +
      r194->data[r194->size[0] * i6]) + r196->data[r196->size[0] * i6]) +
      r199->data[r199->size[0] * i6]) + r201->data[r201->size[0] * i6]) +
      r204->data[r204->size[0] * i6]) + r206->data[r206->size[0] * i6]) +
      r211->data[r211->size[0] * i6]) + r215->data[r215->size[0] * i6]) +
      r217->data[r217->size[0] * i6]) + r219->data[r219->size[0] * i6])) -
      X->data[4 + X->size[0] * i6]) - X->data[5 + X->size[0] * i6]) - X->data[6
      + X->size[0] * i6] > 2.5);
  }

  emxFree_real_T(&r276);
  emxFree_real_T(&r274);
  emxFree_real_T(&r269);
  emxFree_real_T(&r219);
  emxFree_real_T(&r209);
  emxFree_real_T(&r204);
  emxFree_real_T(&r199);
  emxFree_real_T(&r194);
  emxFree_real_T(&r189);
  emxFree_real_T(&r184);
  emxFree_real_T(&r179);
  emxFree_real_T(&r174);
  emxFree_real_T(&r169);
  emxFree_real_T(&r164);
  emxFree_real_T(&r159);
  emxFree_real_T(&r217);
  emxFree_real_T(&r215);
  emxFree_real_T(&r211);
  emxFree_real_T(&r206);
  emxFree_real_T(&r201);
  emxFree_real_T(&r196);
  emxFree_real_T(&r191);
  emxFree_real_T(&r186);
  emxFree_real_T(&r181);
  emxFree_real_T(&r176);
  emxFree_real_T(&r171);
  emxFree_real_T(&r166);
  emxFree_real_T(&r161);
  emxFree_real_T(&r157);
  emxFree_real_T(&r155);
}

/*
 * File trailer for ThresholdEqnCurrent.c
 *
 * [EOF]
 */
