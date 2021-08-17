/*
 * File: ThresholdEqnResistance.c
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
#include "ThresholdEqnResistance.h"
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
void ThresholdEqnResistance(const emxArray_real_T *X, emxArray_boolean_T *B)
{
  emxArray_real_T *Tb;
  int loop_ub;
  int i2;
  emxArray_real_T *b_X;
  emxArray_real_T *xpS;
  emxArray_real_T *r1;
  emxArray_real_T *b;
  emxArray_real_T *r2;
  emxArray_real_T *r3;
  emxArray_real_T *r4;
  emxArray_real_T *r5;
  emxArray_real_T *r6;
  emxArray_real_T *r7;
  emxArray_real_T *r8;
  emxArray_real_T *r9;
  emxArray_real_T *r10;
  emxArray_real_T *r11;
  emxArray_real_T *r12;
  emxArray_real_T *r13;
  emxArray_real_T *r14;
  emxArray_real_T *r15;
  emxArray_real_T *r16;
  emxArray_real_T *r17;
  emxArray_real_T *r18;
  emxArray_real_T *r19;
  emxArray_real_T *r20;
  emxArray_real_T *r21;
  emxArray_real_T *r22;
  emxArray_real_T *r23;
  emxArray_real_T *r24;
  emxArray_real_T *r25;
  emxArray_real_T *r26;
  emxArray_real_T *r27;
  emxArray_real_T *r28;
  emxArray_real_T *r29;
  emxArray_real_T *r30;
  emxArray_real_T *r31;
  emxArray_real_T *r32;
  emxArray_real_T *r33;
  emxArray_real_T *r34;
  emxArray_real_T *r35;
  emxArray_real_T *r36;
  emxArray_real_T *r37;
  emxArray_real_T *r38;
  emxArray_real_T *r39;
  emxArray_real_T *r40;
  emxArray_real_T *r41;
  emxArray_real_T *r42;
  emxArray_real_T *r43;
  emxArray_real_T *r44;
  emxArray_real_T *r45;
  emxArray_real_T *r46;
  emxArray_real_T *r47;
  emxArray_real_T *r48;
  emxArray_real_T *r49;
  emxArray_real_T *r50;
  emxArray_real_T *r51;
  emxArray_real_T *r52;
  emxArray_real_T *r53;
  emxArray_real_T *r54;
  emxArray_real_T *r55;
  emxArray_real_T *r56;
  emxArray_real_T *r57;
  emxArray_real_T *r58;
  emxArray_real_T *r59;
  emxArray_real_T *r60;
  emxArray_real_T *c_X;
  emxArray_real_T *xnS;
  emxArray_real_T *r61;
  emxArray_real_T *b_b;
  emxArray_real_T *r62;
  emxArray_real_T *r63;
  emxArray_real_T *r64;
  emxArray_real_T *r65;
  emxArray_real_T *r66;
  emxArray_real_T *r67;
  emxArray_real_T *r68;
  emxArray_real_T *r69;
  emxArray_real_T *r70;
  emxArray_real_T *r71;
  emxArray_real_T *r72;
  emxArray_real_T *r73;
  emxArray_real_T *r74;
  emxArray_real_T *r75;
  emxArray_real_T *r76;
  emxArray_real_T *r77;
  emxArray_real_T *r78;
  emxArray_real_T *r79;
  emxArray_real_T *r80;
  emxArray_real_T *r81;
  emxArray_real_T *r82;
  emxArray_real_T *r83;
  emxArray_real_T *r84;
  emxArray_real_T *r85;
  emxArray_real_T *r86;
  emxArray_real_T *r87;
  emxArray_real_T *r88;
  emxArray_real_T *r89;
  emxArray_real_T *r90;
  emxArray_real_T *r91;
  emxArray_real_T *r92;
  emxArray_real_T *r93;
  emxArray_real_T *r94;
  emxArray_real_T *r95;
  emxArray_real_T *r96;
  emxArray_real_T *r97;
  emxArray_real_T *r98;
  emxArray_real_T *r99;
  emxArray_real_T *r100;
  emxArray_real_T *r101;
  emxArray_real_T *r102;
  emxArray_real_T *r103;
  emxArray_real_T *r104;
  emxArray_real_T *r105;
  emxArray_real_T *r106;
  emxArray_real_T *r107;
  emxArray_real_T *r108;
  emxArray_real_T *r109;
  emxArray_real_T *r110;
  emxArray_real_T *r111;
  emxArray_real_T *r112;
  emxArray_real_T *r113;
  emxArray_real_T *r114;
  emxArray_real_T *r115;
  emxArray_real_T *r116;
  emxArray_real_T *r117;
  emxArray_real_T *r118;
  emxArray_real_T *r119;
  emxArray_real_T *r120;
  emxArray_real_T *r121;
  emxArray_real_T *r122;
  emxArray_real_T *r123;
  emxArray_real_T *r124;
  emxArray_real_T *r125;
  emxArray_real_T *r126;
  emxArray_real_T *r127;
  emxArray_real_T *r128;
  emxArray_real_T *r129;
  emxArray_real_T *r130;
  emxArray_real_T *r131;
  emxArray_real_T *r132;
  emxArray_real_T *r133;
  emxArray_real_T *r134;
  emxArray_real_T *r135;
  emxArray_real_T *r136;
  emxArray_real_T *r137;
  emxArray_real_T *r138;
  emxArray_real_T *r139;
  emxArray_real_T *r140;
  emxArray_real_T *r141;
  emxArray_real_T *r142;
  emxArray_real_T *r143;
  emxArray_real_T *r144;
  emxArray_real_T *r145;
  emxArray_real_T *r146;
  emxArray_real_T *r147;
  emxArray_real_T *r148;
  emxArray_real_T *r149;
  emxArray_real_T *r150;
  emxArray_real_T *r151;
  emxArray_real_T *r152;
  emxInit_real_T(&Tb, 2);

  /*  extract states */
  loop_ub = X->size[1];
  i2 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i2, (int)sizeof(double));
  for (i2 = 0; i2 < loop_ub; i2++) {
    Tb->data[Tb->size[0] * i2] = X->data[7 + X->size[0] * i2];
  }

  emxInit_real_T(&b_X, 2);

  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  loop_ub = X->size[1];
  i2 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i2, (int)sizeof(double));
  for (i2 = 0; i2 < loop_ub; i2++) {
    b_X->data[b_X->size[0] * i2] = X->data[X->size[0] * i2];
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r1, 2);
  rdivide(b_X, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i2 = r1->size[0] * r1->size[1];
  r1->size[0] = 1;
  r1->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r1, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&b_X);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r1->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r2, 2);
  power(r1, b);
  i2 = r2->size[0] * r2->size[1];
  r2->size[0] = 1;
  r2->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r2, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r1);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r2->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r3, 2);
  emxInit_real_T(&r4, 2);
  b_power(r2, r3);
  i2 = r4->size[0] * r4->size[1];
  r4->size[0] = 1;
  r4->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r4, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r2);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r4->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r5, 2);
  emxInit_real_T(&r6, 2);
  c_power(r4, r5);
  i2 = r6->size[0] * r6->size[1];
  r6->size[0] = 1;
  r6->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r6, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r4);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r6->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r7, 2);
  emxInit_real_T(&r8, 2);
  d_power(r6, r7);
  i2 = r8->size[0] * r8->size[1];
  r8->size[0] = 1;
  r8->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r8, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r6);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r8->data[i2] = 2.0 * xpS->data[i2] * 2.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r9, 2);
  emxInit_real_T(&r10, 2);
  b_rdivide(r8, r7, r9);
  i2 = r10->size[0] * r10->size[1];
  r10->size[0] = 1;
  r10->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r10, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r8);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r10->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r11, 2);
  e_power(r10, r7);
  i2 = r11->size[0] * r11->size[1];
  r11->size[0] = 1;
  r11->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r11, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r10);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r11->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r12, 2);
  emxInit_real_T(&r13, 2);
  f_power(r11, r12);
  i2 = r13->size[0] * r13->size[1];
  r13->size[0] = 1;
  r13->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r13, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r11);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r13->data[i2] = 2.0 * xpS->data[i2] * 3.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r14, 2);
  emxInit_real_T(&r15, 2);
  b_rdivide(r13, r12, r14);
  i2 = r15->size[0] * r15->size[1];
  r15->size[0] = 1;
  r15->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r15, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r13);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r15->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r16, 2);
  g_power(r15, r12);
  i2 = r16->size[0] * r16->size[1];
  r16->size[0] = 1;
  r16->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r16, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r15);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r16->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r17, 2);
  emxInit_real_T(&r18, 2);
  h_power(r16, r17);
  i2 = r18->size[0] * r18->size[1];
  r18->size[0] = 1;
  r18->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r18, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r16);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r18->data[i2] = 2.0 * xpS->data[i2] * 4.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r19, 2);
  emxInit_real_T(&r20, 2);
  b_rdivide(r18, r17, r19);
  i2 = r20->size[0] * r20->size[1];
  r20->size[0] = 1;
  r20->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r20, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r18);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r20->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r21, 2);
  i_power(r20, r17);
  i2 = r21->size[0] * r21->size[1];
  r21->size[0] = 1;
  r21->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r21, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r20);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r21->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r22, 2);
  emxInit_real_T(&r23, 2);
  j_power(r21, r22);
  i2 = r23->size[0] * r23->size[1];
  r23->size[0] = 1;
  r23->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r23, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r21);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r23->data[i2] = 2.0 * xpS->data[i2] * 5.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r24, 2);
  emxInit_real_T(&r25, 2);
  b_rdivide(r23, r22, r24);
  i2 = r25->size[0] * r25->size[1];
  r25->size[0] = 1;
  r25->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r25, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r23);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r25->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r26, 2);
  k_power(r25, r22);
  i2 = r26->size[0] * r26->size[1];
  r26->size[0] = 1;
  r26->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r26, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r25);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r26->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r27, 2);
  emxInit_real_T(&r28, 2);
  l_power(r26, r27);
  i2 = r28->size[0] * r28->size[1];
  r28->size[0] = 1;
  r28->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r28, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r26);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r28->data[i2] = 2.0 * xpS->data[i2] * 6.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r29, 2);
  emxInit_real_T(&r30, 2);
  b_rdivide(r28, r27, r29);
  i2 = r30->size[0] * r30->size[1];
  r30->size[0] = 1;
  r30->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r30, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r28);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r30->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r31, 2);
  m_power(r30, r27);
  i2 = r31->size[0] * r31->size[1];
  r31->size[0] = 1;
  r31->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r31, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r30);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r31->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r32, 2);
  emxInit_real_T(&r33, 2);
  n_power(r31, r32);
  i2 = r33->size[0] * r33->size[1];
  r33->size[0] = 1;
  r33->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r33, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r31);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r33->data[i2] = 2.0 * xpS->data[i2] * 7.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r34, 2);
  emxInit_real_T(&r35, 2);
  b_rdivide(r33, r32, r34);
  i2 = r35->size[0] * r35->size[1];
  r35->size[0] = 1;
  r35->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r35, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r33);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r35->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r36, 2);
  o_power(r35, r32);
  i2 = r36->size[0] * r36->size[1];
  r36->size[0] = 1;
  r36->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r36, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r35);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r36->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r37, 2);
  emxInit_real_T(&r38, 2);
  p_power(r36, r37);
  i2 = r38->size[0] * r38->size[1];
  r38->size[0] = 1;
  r38->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r38, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r36);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r38->data[i2] = 2.0 * xpS->data[i2] * 8.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r39, 2);
  emxInit_real_T(&r40, 2);
  b_rdivide(r38, r37, r39);
  i2 = r40->size[0] * r40->size[1];
  r40->size[0] = 1;
  r40->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r40, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r38);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r40->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r41, 2);
  q_power(r40, r37);
  i2 = r41->size[0] * r41->size[1];
  r41->size[0] = 1;
  r41->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r41, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r40);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r41->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r42, 2);
  emxInit_real_T(&r43, 2);
  r_power(r41, r42);
  i2 = r43->size[0] * r43->size[1];
  r43->size[0] = 1;
  r43->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r43, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r41);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r43->data[i2] = 2.0 * xpS->data[i2] * 9.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r44, 2);
  emxInit_real_T(&r45, 2);
  b_rdivide(r43, r42, r44);
  i2 = r45->size[0] * r45->size[1];
  r45->size[0] = 1;
  r45->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r45, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r43);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r45->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r46, 2);
  s_power(r45, r42);
  i2 = r46->size[0] * r46->size[1];
  r46->size[0] = 1;
  r46->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r46, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r45);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r46->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r47, 2);
  emxInit_real_T(&r48, 2);
  t_power(r46, r47);
  i2 = r48->size[0] * r48->size[1];
  r48->size[0] = 1;
  r48->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r48, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r46);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r48->data[i2] = 2.0 * xpS->data[i2] * 10.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r49, 2);
  emxInit_real_T(&r50, 2);
  b_rdivide(r48, r47, r49);
  i2 = r50->size[0] * r50->size[1];
  r50->size[0] = 1;
  r50->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r50, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r48);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r50->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r51, 2);
  u_power(r50, r47);
  i2 = r51->size[0] * r51->size[1];
  r51->size[0] = 1;
  r51->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r51, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r50);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r51->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r52, 2);
  emxInit_real_T(&r53, 2);
  v_power(r51, r52);
  i2 = r53->size[0] * r53->size[1];
  r53->size[0] = 1;
  r53->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r53, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r51);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r53->data[i2] = 2.0 * xpS->data[i2] * 11.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r54, 2);
  emxInit_real_T(&r55, 2);
  b_rdivide(r53, r52, r54);
  i2 = r55->size[0] * r55->size[1];
  r55->size[0] = 1;
  r55->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r55, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r53);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r55->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r56, 2);
  w_power(r55, r52);
  i2 = r56->size[0] * r56->size[1];
  r56->size[0] = 1;
  r56->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r56, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r55);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r56->data[i2] = 2.0 * xpS->data[i2] - 1.0;
  }

  emxInit_real_T(&r57, 2);
  emxInit_real_T(&r58, 2);
  x_power(r56, r57);
  i2 = r58->size[0] * r58->size[1];
  r58->size[0] = 1;
  r58->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r58, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r56);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r58->data[i2] = 2.0 * xpS->data[i2] * 12.0 * (1.0 - xpS->data[i2]);
  }

  emxInit_real_T(&r59, 2);
  emxInit_real_T(&r60, 2);
  b_rdivide(r58, r57, r59);
  i2 = r60->size[0] * r60->size[1];
  r60->size[0] = 1;
  r60->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r60, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r58);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r60->data[i2] = 1.0 - xpS->data[i2];
  }

  emxInit_real_T(&c_X, 2);
  b_rdivide(r60, xpS, r57);
  c_log(r57);

  /*  compute mole fraction at surface, negative electrode */
  loop_ub = X->size[1];
  i2 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i2, (int)sizeof(double));
  emxFree_real_T(&r60);
  for (i2 = 0; i2 < loop_ub; i2++) {
    c_X->data[c_X->size[0] * i2] = X->data[3 + X->size[0] * i2];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r61, 2);
  rdivide(c_X, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i2 = r61->size[0] * r61->size[1];
  r61->size[0] = 1;
  r61->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r61, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&c_X);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r61->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&b_b, 2);
  emxInit_real_T(&r62, 2);
  power(r61, b_b);
  i2 = r62->size[0] * r62->size[1];
  r62->size[0] = 1;
  r62->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r62, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r61);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r62->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r63, 2);
  emxInit_real_T(&r64, 2);
  b_power(r62, r63);
  i2 = r64->size[0] * r64->size[1];
  r64->size[0] = 1;
  r64->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r64, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r62);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r64->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r65, 2);
  emxInit_real_T(&r66, 2);
  c_power(r64, r65);
  i2 = r66->size[0] * r66->size[1];
  r66->size[0] = 1;
  r66->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r66, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r64);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r66->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r67, 2);
  emxInit_real_T(&r68, 2);
  d_power(r66, r67);
  i2 = r68->size[0] * r68->size[1];
  r68->size[0] = 1;
  r68->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r68, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r66);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r68->data[i2] = 2.0 * xnS->data[i2] * 2.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r69, 2);
  emxInit_real_T(&r70, 2);
  b_rdivide(r68, r67, r69);
  i2 = r70->size[0] * r70->size[1];
  r70->size[0] = 1;
  r70->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r70, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r68);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r70->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r71, 2);
  e_power(r70, r67);
  i2 = r71->size[0] * r71->size[1];
  r71->size[0] = 1;
  r71->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r71, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r70);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r71->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r72, 2);
  emxInit_real_T(&r73, 2);
  f_power(r71, r72);
  i2 = r73->size[0] * r73->size[1];
  r73->size[0] = 1;
  r73->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r73, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r71);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r73->data[i2] = 2.0 * xnS->data[i2] * 3.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r74, 2);
  emxInit_real_T(&r75, 2);
  b_rdivide(r73, r72, r74);
  i2 = r75->size[0] * r75->size[1];
  r75->size[0] = 1;
  r75->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r75, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r73);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r75->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r76, 2);
  g_power(r75, r72);
  i2 = r76->size[0] * r76->size[1];
  r76->size[0] = 1;
  r76->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r76, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r75);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r76->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r77, 2);
  emxInit_real_T(&r78, 2);
  h_power(r76, r77);
  i2 = r78->size[0] * r78->size[1];
  r78->size[0] = 1;
  r78->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r78, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r76);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r78->data[i2] = 2.0 * xnS->data[i2] * 4.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r79, 2);
  emxInit_real_T(&r80, 2);
  b_rdivide(r78, r77, r79);
  i2 = r80->size[0] * r80->size[1];
  r80->size[0] = 1;
  r80->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r80, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r78);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r80->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r81, 2);
  i_power(r80, r77);
  i2 = r81->size[0] * r81->size[1];
  r81->size[0] = 1;
  r81->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r81, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r80);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r81->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r82, 2);
  emxInit_real_T(&r83, 2);
  j_power(r81, r82);
  i2 = r83->size[0] * r83->size[1];
  r83->size[0] = 1;
  r83->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r83, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r81);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r83->data[i2] = 2.0 * xnS->data[i2] * 5.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r84, 2);
  emxInit_real_T(&r85, 2);
  b_rdivide(r83, r82, r84);
  i2 = r85->size[0] * r85->size[1];
  r85->size[0] = 1;
  r85->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r85, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r83);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r85->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r86, 2);
  k_power(r85, r82);
  i2 = r86->size[0] * r86->size[1];
  r86->size[0] = 1;
  r86->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r86, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r85);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r86->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r87, 2);
  emxInit_real_T(&r88, 2);
  l_power(r86, r87);
  i2 = r88->size[0] * r88->size[1];
  r88->size[0] = 1;
  r88->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r88, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r86);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r88->data[i2] = 2.0 * xnS->data[i2] * 6.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r89, 2);
  emxInit_real_T(&r90, 2);
  b_rdivide(r88, r87, r89);
  i2 = r90->size[0] * r90->size[1];
  r90->size[0] = 1;
  r90->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r90, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r88);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r90->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r91, 2);
  m_power(r90, r87);
  i2 = r91->size[0] * r91->size[1];
  r91->size[0] = 1;
  r91->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r91, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r90);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r91->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r92, 2);
  emxInit_real_T(&r93, 2);
  n_power(r91, r92);
  i2 = r93->size[0] * r93->size[1];
  r93->size[0] = 1;
  r93->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r93, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r91);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r93->data[i2] = 2.0 * xnS->data[i2] * 7.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r94, 2);
  emxInit_real_T(&r95, 2);
  b_rdivide(r93, r92, r94);
  i2 = r95->size[0] * r95->size[1];
  r95->size[0] = 1;
  r95->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r95, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r93);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r95->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r96, 2);
  o_power(r95, r92);
  i2 = r96->size[0] * r96->size[1];
  r96->size[0] = 1;
  r96->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r96, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r95);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r96->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r97, 2);
  emxInit_real_T(&r98, 2);
  p_power(r96, r97);
  i2 = r98->size[0] * r98->size[1];
  r98->size[0] = 1;
  r98->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r98, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r96);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r98->data[i2] = 2.0 * xnS->data[i2] * 8.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r99, 2);
  emxInit_real_T(&r100, 2);
  b_rdivide(r98, r97, r99);
  i2 = r100->size[0] * r100->size[1];
  r100->size[0] = 1;
  r100->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r100, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r98);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r100->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r101, 2);
  q_power(r100, r97);
  i2 = r101->size[0] * r101->size[1];
  r101->size[0] = 1;
  r101->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r101, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r100);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r101->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r102, 2);
  emxInit_real_T(&r103, 2);
  r_power(r101, r102);
  i2 = r103->size[0] * r103->size[1];
  r103->size[0] = 1;
  r103->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r103, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r101);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r103->data[i2] = 2.0 * xnS->data[i2] * 9.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r104, 2);
  emxInit_real_T(&r105, 2);
  b_rdivide(r103, r102, r104);
  i2 = r105->size[0] * r105->size[1];
  r105->size[0] = 1;
  r105->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r105, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r103);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r105->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r106, 2);
  s_power(r105, r102);
  i2 = r106->size[0] * r106->size[1];
  r106->size[0] = 1;
  r106->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r106, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r105);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r106->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r107, 2);
  emxInit_real_T(&r108, 2);
  t_power(r106, r107);
  i2 = r108->size[0] * r108->size[1];
  r108->size[0] = 1;
  r108->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r108, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r106);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r108->data[i2] = 2.0 * xnS->data[i2] * 10.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r109, 2);
  emxInit_real_T(&r110, 2);
  b_rdivide(r108, r107, r109);
  i2 = r110->size[0] * r110->size[1];
  r110->size[0] = 1;
  r110->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r110, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r108);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r110->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r111, 2);
  u_power(r110, r107);
  i2 = r111->size[0] * r111->size[1];
  r111->size[0] = 1;
  r111->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r111, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r110);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r111->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r112, 2);
  emxInit_real_T(&r113, 2);
  v_power(r111, r112);
  i2 = r113->size[0] * r113->size[1];
  r113->size[0] = 1;
  r113->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r113, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r111);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r113->data[i2] = 2.0 * xnS->data[i2] * 11.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r114, 2);
  emxInit_real_T(&r115, 2);
  b_rdivide(r113, r112, r114);
  i2 = r115->size[0] * r115->size[1];
  r115->size[0] = 1;
  r115->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r115, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r113);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r115->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r116, 2);
  w_power(r115, r112);
  i2 = r116->size[0] * r116->size[1];
  r116->size[0] = 1;
  r116->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r116, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r115);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r116->data[i2] = 2.0 * xnS->data[i2] - 1.0;
  }

  emxInit_real_T(&r117, 2);
  emxInit_real_T(&r118, 2);
  x_power(r116, r117);
  i2 = r118->size[0] * r118->size[1];
  r118->size[0] = 1;
  r118->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r118, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r116);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r118->data[i2] = 2.0 * xnS->data[i2] * 12.0 * (1.0 - xnS->data[i2]);
  }

  emxInit_real_T(&r119, 2);
  emxInit_real_T(&r120, 2);
  b_rdivide(r118, r117, r119);
  i2 = r120->size[0] * r120->size[1];
  r120->size[0] = 1;
  r120->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r120, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r118);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r120->data[i2] = 1.0 - xnS->data[i2];
  }

  emxInit_real_T(&r121, 2);
  b_rdivide(r120, xnS, r117);
  c_log(r117);

  /*  voltages */
  /*  individual performance constraints */
  /*  at EOL when any fail */
  i2 = r121->size[0] * r121->size[1];
  r121->size[0] = 1;
  r121->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r121, i2, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r120);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r121->data[i2] = 8.3144621 * Tb->data[i2];
  }

  emxInit_real_T(&r122, 2);
  emxInit_real_T(&r123, 2);
  rdivide(r121, 96487.0, r122);
  i2 = r123->size[0] * r123->size[1];
  r123->size[0] = 1;
  r123->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r123, i2, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r121);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r123->data[i2] = -31593.7 * b->data[i2];
  }

  emxInit_real_T(&r124, 2);
  emxInit_real_T(&r125, 2);
  rdivide(r123, 96487.0, r124);
  i2 = r125->size[0] * r125->size[1];
  r125->size[0] = 1;
  r125->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r125, i2, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r123);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r125->data[i2] = 2.0 * xpS->data[i2] * (1.0 - xpS->data[i2]);
  }

  emxFree_real_T(&xpS);
  emxInit_real_T(&r126, 2);
  rdivide(r125, 1.0, b);
  i2 = r126->size[0] * r126->size[1];
  r126->size[0] = 1;
  r126->size[1] = r3->size[1];
  emxEnsureCapacity((emxArray__common *)r126, i2, (int)sizeof(double));
  loop_ub = r3->size[0] * r3->size[1];
  emxFree_real_T(&r125);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r126->data[i2] = 0.106747 * (r3->data[i2] - b->data[i2]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r127, 2);
  rdivide(r126, 96487.0, r3);
  i2 = r127->size[0] * r127->size[1];
  r127->size[0] = 1;
  r127->size[1] = r5->size[1];
  emxEnsureCapacity((emxArray__common *)r127, i2, (int)sizeof(double));
  loop_ub = r5->size[0] * r5->size[1];
  emxFree_real_T(&r126);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r127->data[i2] = 24606.4 * (r5->data[i2] - r9->data[i2]);
  }

  emxInit_real_T(&r128, 2);
  rdivide(r127, 96487.0, r5);
  i2 = r128->size[0] * r128->size[1];
  r128->size[0] = 1;
  r128->size[1] = r7->size[1];
  emxEnsureCapacity((emxArray__common *)r128, i2, (int)sizeof(double));
  loop_ub = r7->size[0] * r7->size[1];
  emxFree_real_T(&r127);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r128->data[i2] = -78561.9 * (r7->data[i2] - r14->data[i2]);
  }

  emxInit_real_T(&r129, 2);
  rdivide(r128, 96487.0, r7);
  i2 = r129->size[0] * r129->size[1];
  r129->size[0] = 1;
  r129->size[1] = r12->size[1];
  emxEnsureCapacity((emxArray__common *)r129, i2, (int)sizeof(double));
  loop_ub = r12->size[0] * r12->size[1];
  emxFree_real_T(&r128);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r129->data[i2] = 13317.9 * (r12->data[i2] - r19->data[i2]);
  }

  emxInit_real_T(&r130, 2);
  rdivide(r129, 96487.0, r9);
  i2 = r130->size[0] * r130->size[1];
  r130->size[0] = 1;
  r130->size[1] = r17->size[1];
  emxEnsureCapacity((emxArray__common *)r130, i2, (int)sizeof(double));
  loop_ub = r17->size[0] * r17->size[1];
  emxFree_real_T(&r129);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r130->data[i2] = 307387.0 * (r17->data[i2] - r24->data[i2]);
  }

  emxInit_real_T(&r131, 2);
  rdivide(r130, 96487.0, r12);
  i2 = r131->size[0] * r131->size[1];
  r131->size[0] = 1;
  r131->size[1] = r22->size[1];
  emxEnsureCapacity((emxArray__common *)r131, i2, (int)sizeof(double));
  loop_ub = r22->size[0] * r22->size[1];
  emxFree_real_T(&r130);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r131->data[i2] = 84916.1 * (r22->data[i2] - r29->data[i2]);
  }

  emxInit_real_T(&r132, 2);
  rdivide(r131, 96487.0, r14);
  i2 = r132->size[0] * r132->size[1];
  r132->size[0] = 1;
  r132->size[1] = r27->size[1];
  emxEnsureCapacity((emxArray__common *)r132, i2, (int)sizeof(double));
  loop_ub = r27->size[0] * r27->size[1];
  emxFree_real_T(&r131);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r132->data[i2] = -1.07469E+6 * (r27->data[i2] - r34->data[i2]);
  }

  emxInit_real_T(&r133, 2);
  rdivide(r132, 96487.0, r17);
  i2 = r133->size[0] * r133->size[1];
  r133->size[0] = 1;
  r133->size[1] = r32->size[1];
  emxEnsureCapacity((emxArray__common *)r133, i2, (int)sizeof(double));
  loop_ub = r32->size[0] * r32->size[1];
  emxFree_real_T(&r132);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r133->data[i2] = 2285.04 * (r32->data[i2] - r39->data[i2]);
  }

  emxInit_real_T(&r134, 2);
  rdivide(r133, 96487.0, r19);
  i2 = r134->size[0] * r134->size[1];
  r134->size[0] = 1;
  r134->size[1] = r37->size[1];
  emxEnsureCapacity((emxArray__common *)r134, i2, (int)sizeof(double));
  loop_ub = r37->size[0] * r37->size[1];
  emxFree_real_T(&r133);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r134->data[i2] = 990894.0 * (r37->data[i2] - r44->data[i2]);
  }

  emxInit_real_T(&r135, 2);
  rdivide(r134, 96487.0, r22);
  i2 = r135->size[0] * r135->size[1];
  r135->size[0] = 1;
  r135->size[1] = r42->size[1];
  emxEnsureCapacity((emxArray__common *)r135, i2, (int)sizeof(double));
  loop_ub = r42->size[0] * r42->size[1];
  emxFree_real_T(&r134);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r135->data[i2] = 283920.0 * (r42->data[i2] - r49->data[i2]);
  }

  emxInit_real_T(&r136, 2);
  rdivide(r135, 96487.0, r24);
  i2 = r136->size[0] * r136->size[1];
  r136->size[0] = 1;
  r136->size[1] = r47->size[1];
  emxEnsureCapacity((emxArray__common *)r136, i2, (int)sizeof(double));
  loop_ub = r47->size[0] * r47->size[1];
  emxFree_real_T(&r135);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r136->data[i2] = -161513.0 * (r47->data[i2] - r54->data[i2]);
  }

  emxInit_real_T(&r137, 2);
  rdivide(r136, 96487.0, r27);
  i2 = r137->size[0] * r137->size[1];
  r137->size[0] = 1;
  r137->size[1] = r52->size[1];
  emxEnsureCapacity((emxArray__common *)r137, i2, (int)sizeof(double));
  loop_ub = r52->size[0] * r52->size[1];
  emxFree_real_T(&r136);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r137->data[i2] = -469218.0 * (r52->data[i2] - r59->data[i2]);
  }

  emxInit_real_T(&r138, 2);
  rdivide(r137, 96487.0, r29);
  i2 = r138->size[0] * r138->size[1];
  r138->size[0] = 1;
  r138->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r138, i2, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r137);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r138->data[i2] = 8.3144621 * Tb->data[i2];
  }

  emxFree_real_T(&Tb);
  emxInit_real_T(&r139, 2);
  rdivide(r138, 96487.0, r32);
  i2 = r139->size[0] * r139->size[1];
  r139->size[0] = 1;
  r139->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r139, i2, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r138);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r139->data[i2] = 86.19 * b_b->data[i2];
  }

  emxFree_real_T(&b_b);
  emxInit_real_T(&r140, 2);
  rdivide(r139, 96487.0, r34);
  i2 = r140->size[0] * r140->size[1];
  r140->size[0] = 1;
  r140->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r140, i2, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r139);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r140->data[i2] = 2.0 * xnS->data[i2] * (1.0 - xnS->data[i2]);
  }

  emxFree_real_T(&xnS);
  emxInit_real_T(&r141, 2);
  rdivide(r140, 1.0, r37);
  i2 = r141->size[0] * r141->size[1];
  r141->size[0] = 1;
  r141->size[1] = r63->size[1];
  emxEnsureCapacity((emxArray__common *)r141, i2, (int)sizeof(double));
  loop_ub = r63->size[0] * r63->size[1];
  emxFree_real_T(&r140);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r141->data[i2] = 0.0 * (r63->data[i2] - r37->data[i2]);
  }

  emxInit_real_T(&r142, 2);
  rdivide(r141, 96487.0, r37);
  i2 = r142->size[0] * r142->size[1];
  r142->size[0] = 1;
  r142->size[1] = r65->size[1];
  emxEnsureCapacity((emxArray__common *)r142, i2, (int)sizeof(double));
  loop_ub = r65->size[0] * r65->size[1];
  emxFree_real_T(&r141);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r142->data[i2] = 0.0 * (r65->data[i2] - r69->data[i2]);
  }

  emxFree_real_T(&r69);
  emxInit_real_T(&r143, 2);
  rdivide(r142, 96487.0, r39);
  i2 = r143->size[0] * r143->size[1];
  r143->size[0] = 1;
  r143->size[1] = r67->size[1];
  emxEnsureCapacity((emxArray__common *)r143, i2, (int)sizeof(double));
  loop_ub = r67->size[0] * r67->size[1];
  emxFree_real_T(&r142);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r143->data[i2] = 0.0 * (r67->data[i2] - r74->data[i2]);
  }

  emxFree_real_T(&r74);
  emxInit_real_T(&r144, 2);
  rdivide(r143, 96487.0, r42);
  i2 = r144->size[0] * r144->size[1];
  r144->size[0] = 1;
  r144->size[1] = r72->size[1];
  emxEnsureCapacity((emxArray__common *)r144, i2, (int)sizeof(double));
  loop_ub = r72->size[0] * r72->size[1];
  emxFree_real_T(&r143);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r144->data[i2] = 0.0 * (r72->data[i2] - r79->data[i2]);
  }

  emxFree_real_T(&r72);
  emxFree_real_T(&r79);
  emxInit_real_T(&r145, 2);
  rdivide(r144, 96487.0, r44);
  i2 = r145->size[0] * r145->size[1];
  r145->size[0] = 1;
  r145->size[1] = r77->size[1];
  emxEnsureCapacity((emxArray__common *)r145, i2, (int)sizeof(double));
  loop_ub = r77->size[0] * r77->size[1];
  emxFree_real_T(&r144);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r145->data[i2] = 0.0 * (r77->data[i2] - r84->data[i2]);
  }

  emxFree_real_T(&r77);
  emxFree_real_T(&r84);
  emxInit_real_T(&r146, 2);
  rdivide(r145, 96487.0, r47);
  i2 = r146->size[0] * r146->size[1];
  r146->size[0] = 1;
  r146->size[1] = r82->size[1];
  emxEnsureCapacity((emxArray__common *)r146, i2, (int)sizeof(double));
  loop_ub = r82->size[0] * r82->size[1];
  emxFree_real_T(&r145);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r146->data[i2] = 0.0 * (r82->data[i2] - r89->data[i2]);
  }

  emxFree_real_T(&r82);
  emxFree_real_T(&r89);
  emxInit_real_T(&r147, 2);
  rdivide(r146, 96487.0, r49);
  i2 = r147->size[0] * r147->size[1];
  r147->size[0] = 1;
  r147->size[1] = r87->size[1];
  emxEnsureCapacity((emxArray__common *)r147, i2, (int)sizeof(double));
  loop_ub = r87->size[0] * r87->size[1];
  emxFree_real_T(&r146);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r147->data[i2] = 0.0 * (r87->data[i2] - r94->data[i2]);
  }

  emxFree_real_T(&r87);
  emxFree_real_T(&r94);
  emxInit_real_T(&r148, 2);
  rdivide(r147, 96487.0, r52);
  i2 = r148->size[0] * r148->size[1];
  r148->size[0] = 1;
  r148->size[1] = r92->size[1];
  emxEnsureCapacity((emxArray__common *)r148, i2, (int)sizeof(double));
  loop_ub = r92->size[0] * r92->size[1];
  emxFree_real_T(&r147);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r148->data[i2] = 0.0 * (r92->data[i2] - r99->data[i2]);
  }

  emxFree_real_T(&r92);
  emxFree_real_T(&r99);
  emxInit_real_T(&r149, 2);
  rdivide(r148, 96487.0, r54);
  i2 = r149->size[0] * r149->size[1];
  r149->size[0] = 1;
  r149->size[1] = r97->size[1];
  emxEnsureCapacity((emxArray__common *)r149, i2, (int)sizeof(double));
  loop_ub = r97->size[0] * r97->size[1];
  emxFree_real_T(&r148);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r149->data[i2] = 0.0 * (r97->data[i2] - r104->data[i2]);
  }

  emxFree_real_T(&r97);
  emxFree_real_T(&r104);
  emxInit_real_T(&r150, 2);
  rdivide(r149, 96487.0, r59);
  i2 = r150->size[0] * r150->size[1];
  r150->size[0] = 1;
  r150->size[1] = r102->size[1];
  emxEnsureCapacity((emxArray__common *)r150, i2, (int)sizeof(double));
  loop_ub = r102->size[0] * r102->size[1];
  emxFree_real_T(&r149);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r150->data[i2] = 0.0 * (r102->data[i2] - r109->data[i2]);
  }

  emxFree_real_T(&r102);
  emxFree_real_T(&r109);
  emxInit_real_T(&r151, 2);
  rdivide(r150, 96487.0, r63);
  i2 = r151->size[0] * r151->size[1];
  r151->size[0] = 1;
  r151->size[1] = r107->size[1];
  emxEnsureCapacity((emxArray__common *)r151, i2, (int)sizeof(double));
  loop_ub = r107->size[0] * r107->size[1];
  emxFree_real_T(&r150);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r151->data[i2] = 0.0 * (r107->data[i2] - r114->data[i2]);
  }

  emxFree_real_T(&r107);
  emxFree_real_T(&r114);
  emxInit_real_T(&r152, 2);
  rdivide(r151, 96487.0, r65);
  i2 = r152->size[0] * r152->size[1];
  r152->size[0] = 1;
  r152->size[1] = r112->size[1];
  emxEnsureCapacity((emxArray__common *)r152, i2, (int)sizeof(double));
  loop_ub = r112->size[0] * r112->size[1];
  emxFree_real_T(&r151);
  for (i2 = 0; i2 < loop_ub; i2++) {
    r152->data[i2] = 0.0 * (r112->data[i2] - r119->data[i2]);
  }

  emxFree_real_T(&r112);
  emxFree_real_T(&r119);
  rdivide(r152, 96487.0, r67);
  i2 = B->size[0] * B->size[1];
  B->size[0] = 1;
  B->size[1] = r122->size[1];
  emxEnsureCapacity((emxArray__common *)B, i2, (int)sizeof(boolean_T));
  loop_ub = r122->size[1];
  emxFree_real_T(&r152);
  for (i2 = 0; i2 < loop_ub; i2++) {
    B->data[B->size[0] * i2] = !((((((((((((((((((4.03 + r122->data[r122->size[0]
      * i2] * r57->data[r57->size[0] * i2]) + r124->data[r124->size[0] * i2]) +
      r3->data[r3->size[0] * i2]) + r5->data[r5->size[0] * i2]) + r7->data
      [r7->size[0] * i2]) + r9->data[r9->size[0] * i2]) + r12->data[r12->size[0]
      * i2]) + r14->data[r14->size[0] * i2]) + r17->data[r17->size[0] * i2]) +
      r19->data[r19->size[0] * i2]) + r22->data[r22->size[0] * i2]) + r24->
      data[r24->size[0] * i2]) + r27->data[r27->size[0] * i2]) + r29->data
      [r29->size[0] * i2]) - ((((((((((((((0.01 + r32->data[r32->size[0] * i2] *
      r117->data[r117->size[0] * i2]) + r34->data[r34->size[0] * i2]) +
      r37->data[r37->size[0] * i2]) + r39->data[r39->size[0] * i2]) + r42->
      data[r42->size[0] * i2]) + r44->data[r44->size[0] * i2]) + r47->data
      [r47->size[0] * i2]) + r49->data[r49->size[0] * i2]) + r52->data[r52->
      size[0] * i2]) + r54->data[r54->size[0] * i2]) + r59->data[r59->size[0] *
      i2]) + r63->data[r63->size[0] * i2]) + r65->data[r65->size[0] * i2]) +
      r67->data[r67->size[0] * i2])) - X->data[4 + X->size[0] * i2]) - X->data[5
      + X->size[0] * i2]) - X->data[6 + X->size[0] * i2] > 2.5);
  }

  emxFree_real_T(&r124);
  emxFree_real_T(&r122);
  emxFree_real_T(&r117);
  emxFree_real_T(&r67);
  emxFree_real_T(&r57);
  emxFree_real_T(&r52);
  emxFree_real_T(&r47);
  emxFree_real_T(&r42);
  emxFree_real_T(&r37);
  emxFree_real_T(&r32);
  emxFree_real_T(&r27);
  emxFree_real_T(&r22);
  emxFree_real_T(&r17);
  emxFree_real_T(&r12);
  emxFree_real_T(&r7);
  emxFree_real_T(&r65);
  emxFree_real_T(&r63);
  emxFree_real_T(&r59);
  emxFree_real_T(&r54);
  emxFree_real_T(&r49);
  emxFree_real_T(&r44);
  emxFree_real_T(&r39);
  emxFree_real_T(&r34);
  emxFree_real_T(&r29);
  emxFree_real_T(&r24);
  emxFree_real_T(&r19);
  emxFree_real_T(&r14);
  emxFree_real_T(&r9);
  emxFree_real_T(&r5);
  emxFree_real_T(&r3);
}

/*
 * File trailer for ThresholdEqnResistance.c
 *
 * [EOF]
 */
