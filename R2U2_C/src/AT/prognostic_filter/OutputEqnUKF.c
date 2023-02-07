/*
 * File: OutputEqnUKF.c
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
#include "OutputEqnUKF.h"
#include "power.h"
#include "BHM_emxutil.h"
#include "rdivide.h"
#include "log.h"
#include "BHM_rtwutil.h"
#include <stdio.h>

/* Function Definitions */

/*
 * This version of the output eqn function does not need P as an argument. It
 *  is needed for the UKF for compilation purposes due to the restrictions on
 *  the use of function handles.
 * Arguments    : const double X_data[]
 *                double Z[2]
 * Return Type  : void
 */
void OutputEqnUKF(const double X_data[], double Z[2])
{
  double xpS;
  double a;
  double xnS;
  double b_a;

  /*  extract states */
  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  xpS = X_data[0] / 1266.666666666667;

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  a = 2.0 * xpS - 1.0;

  /*  compute mole fraction at surface, negative electrode */
  xnS = X_data[3] / 1266.666666666667;

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  b_a = 2.0 * xnS - 1.0;

  /*  voltages */
  /*  set outputs */
  Z[0] = (((((((((((((((((4.03 + 8.3144621 * X_data[7] / 96487.0 * log((1.0 -
    xpS) / xpS)) + -31593.7 * (2.0 * xpS - 1.0) / 96487.0) + 0.106747 * (a * a -
    2.0 * xpS * (1.0 - xpS)) / 96487.0) + 24606.4 * (rt_powd_snf(2.0 * xpS - 1.0,
    3.0) - 2.0 * xpS * 2.0 * (1.0 - xpS) / (1.0 / (2.0 * xpS - 1.0))) / 96487.0)
                      + -78561.9 * (rt_powd_snf(2.0 * xpS - 1.0, 4.0) - 2.0 *
    xpS * 3.0 * (1.0 - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -2.0)) / 96487.0) +
                     13317.9 * (rt_powd_snf(2.0 * xpS - 1.0, 5.0) - 2.0 * xpS *
    4.0 * (1.0 - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -3.0)) / 96487.0) +
                    307387.0 * (rt_powd_snf(2.0 * xpS - 1.0, 6.0) - 2.0 * xpS *
    5.0 * (1.0 - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -4.0)) / 96487.0) + 84916.1
                   * (rt_powd_snf(2.0 * xpS - 1.0, 7.0) - 2.0 * xpS * 6.0 * (1.0
    - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -5.0)) / 96487.0) + -1.07469E+6 *
                  (rt_powd_snf(2.0 * xpS - 1.0, 8.0) - 2.0 * xpS * 7.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -6.0)) / 96487.0) + 2285.04 *
                 (rt_powd_snf(2.0 * xpS - 1.0, 9.0) - 2.0 * xpS * 8.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -7.0)) / 96487.0) + 990894.0 *
                (rt_powd_snf(2.0 * xpS - 1.0, 10.0) - 2.0 * xpS * 9.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -8.0)) / 96487.0) + 283920.0 *
               (rt_powd_snf(2.0 * xpS - 1.0, 11.0) - 2.0 * xpS * 10.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -9.0)) / 96487.0) + -161513.0 *
              (rt_powd_snf(2.0 * xpS - 1.0, 12.0) - 2.0 * xpS * 11.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -10.0)) / 96487.0) + -469218.0 *
             (rt_powd_snf(2.0 * xpS - 1.0, 13.0) - 2.0 * xpS * 12.0 * (1.0 - xpS)
              / rt_powd_snf(2.0 * xpS - 1.0, -11.0)) / 96487.0) -
            ((((((((((((((0.01 + 8.3144621 * X_data[7] / 96487.0 * log((1.0 -
    xnS) / xnS)) + 86.19 * (2.0 * xnS - 1.0) / 96487.0) + 0.0 * (b_a * b_a - 2.0
    * xnS * (1.0 - xnS)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 3.0) -
    2.0 * xnS * 2.0 * (1.0 - xnS) / (1.0 / (2.0 * xnS - 1.0))) / 96487.0) + 0.0 *
                      (rt_powd_snf(2.0 * xnS - 1.0, 4.0) - 2.0 * xnS * 3.0 *
                       (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -2.0)) /
                      96487.0) + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 5.0) - 2.0 *
    xnS * 4.0 * (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -3.0)) / 96487.0) +
                    0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 6.0) - 2.0 * xnS * 5.0 *
                     (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -4.0)) / 96487.0)
                   + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 7.0) - 2.0 * xnS * 6.0 *
                    (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -5.0)) / 96487.0)
                  + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 8.0) - 2.0 * xnS * 7.0 *
                   (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -6.0)) / 96487.0)
                 + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 9.0) - 2.0 * xnS * 8.0 *
                  (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -7.0)) / 96487.0) +
                0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 10.0) - 2.0 * xnS * 9.0 *
                       (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -8.0)) /
                96487.0) + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 11.0) - 2.0 * xnS
    * 10.0 * (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -9.0)) / 96487.0) + 0.0 *
              (rt_powd_snf(2.0 * xnS - 1.0, 12.0) - 2.0 * xnS * 11.0 * (1.0 -
    xnS) / rt_powd_snf(2.0 * xnS - 1.0, -10.0)) / 96487.0) + 0.0 * (rt_powd_snf
              (2.0 * xnS - 1.0, 13.0) - 2.0 * xnS * 12.0 * (1.0 - xnS) /
              rt_powd_snf(2.0 * xnS - 1.0, -11.0)) / 96487.0)) - X_data[4]) -
          X_data[5]) - X_data[6];
  Z[1] = X_data[7] - 273.15;

  /*  convert to C */
  /*  add noise */
}

/*
 * This version of the output eqn function does not need P as an argument. It
 *  is needed for the UKF for compilation purposes due to the restrictions on
 *  the use of function handles.
 * Arguments    : const emxArray_real_T *X
 *                emxArray_real_T *Z
 * Return Type  : void
 */
void b_OutputEqnUKF(const emxArray_real_T *X, emxArray_real_T *Z)
{
  emxArray_real_T *Tb;
  int loop_ub;
  int i25;
  emxArray_real_T *b_X;
  emxArray_real_T *xpS;
  emxArray_real_T *r813;
  emxArray_real_T *b;
  emxArray_real_T *r814;
  emxArray_real_T *r815;
  emxArray_real_T *r816;
  emxArray_real_T *r817;
  emxArray_real_T *r818;
  emxArray_real_T *r819;
  emxArray_real_T *r820;
  emxArray_real_T *r821;
  emxArray_real_T *r822;
  emxArray_real_T *r823;
  emxArray_real_T *r824;
  emxArray_real_T *r825;
  emxArray_real_T *r826;
  emxArray_real_T *r827;
  emxArray_real_T *r828;
  emxArray_real_T *r829;
  emxArray_real_T *r830;
  emxArray_real_T *r831;
  emxArray_real_T *r832;
  emxArray_real_T *r833;
  emxArray_real_T *r834;
  emxArray_real_T *r835;
  emxArray_real_T *r836;
  emxArray_real_T *r837;
  emxArray_real_T *r838;
  emxArray_real_T *r839;
  emxArray_real_T *r840;
  emxArray_real_T *r841;
  emxArray_real_T *r842;
  emxArray_real_T *r843;
  emxArray_real_T *r844;
  emxArray_real_T *r845;
  emxArray_real_T *r846;
  emxArray_real_T *r847;
  emxArray_real_T *r848;
  emxArray_real_T *r849;
  emxArray_real_T *r850;
  emxArray_real_T *r851;
  emxArray_real_T *r852;
  emxArray_real_T *r853;
  emxArray_real_T *r854;
  emxArray_real_T *r855;
  emxArray_real_T *r856;
  emxArray_real_T *r857;
  emxArray_real_T *r858;
  emxArray_real_T *r859;
  emxArray_real_T *r860;
  emxArray_real_T *r861;
  emxArray_real_T *r862;
  emxArray_real_T *r863;
  emxArray_real_T *r864;
  emxArray_real_T *r865;
  emxArray_real_T *r866;
  emxArray_real_T *r867;
  emxArray_real_T *r868;
  emxArray_real_T *r869;
  emxArray_real_T *r870;
  emxArray_real_T *r871;
  emxArray_real_T *r872;
  emxArray_real_T *c_X;
  emxArray_real_T *xnS;
  emxArray_real_T *r873;
  emxArray_real_T *b_b;
  emxArray_real_T *r874;
  emxArray_real_T *r875;
  emxArray_real_T *r876;
  emxArray_real_T *r877;
  emxArray_real_T *r878;
  emxArray_real_T *r879;
  emxArray_real_T *r880;
  emxArray_real_T *r881;
  emxArray_real_T *r882;
  emxArray_real_T *r883;
  emxArray_real_T *r884;
  emxArray_real_T *r885;
  emxArray_real_T *r886;
  emxArray_real_T *r887;
  emxArray_real_T *r888;
  emxArray_real_T *r889;
  emxArray_real_T *r890;
  emxArray_real_T *r891;
  emxArray_real_T *r892;
  emxArray_real_T *r893;
  emxArray_real_T *r894;
  emxArray_real_T *r895;
  emxArray_real_T *r896;
  emxArray_real_T *r897;
  emxArray_real_T *r898;
  emxArray_real_T *r899;
  emxArray_real_T *r900;
  emxArray_real_T *r901;
  emxArray_real_T *r902;
  emxArray_real_T *r903;
  emxArray_real_T *r904;
  emxArray_real_T *r905;
  emxArray_real_T *r906;
  emxArray_real_T *r907;
  emxArray_real_T *r908;
  emxArray_real_T *r909;
  emxArray_real_T *r910;
  emxArray_real_T *r911;
  emxArray_real_T *r912;
  emxArray_real_T *r913;
  emxArray_real_T *r914;
  emxArray_real_T *r915;
  emxArray_real_T *r916;
  emxArray_real_T *r917;
  emxArray_real_T *r918;
  emxArray_real_T *r919;
  emxArray_real_T *r920;
  emxArray_real_T *r921;
  emxArray_real_T *r922;
  emxArray_real_T *r923;
  emxArray_real_T *r924;
  emxArray_real_T *r925;
  emxArray_real_T *r926;
  emxArray_real_T *r927;
  emxArray_real_T *r928;
  emxArray_real_T *r929;
  emxArray_real_T *r930;
  emxArray_real_T *r931;
  emxArray_real_T *r932;
  emxArray_real_T *r933;
  emxArray_real_T *r934;
  emxArray_real_T *r935;
  emxArray_real_T *r936;
  emxArray_real_T *r937;
  emxArray_real_T *r938;
  emxArray_real_T *r939;
  emxArray_real_T *r940;
  emxArray_real_T *r941;
  emxArray_real_T *r942;
  emxArray_real_T *r943;
  emxArray_real_T *r944;
  emxArray_real_T *r945;
  emxArray_real_T *r946;
  emxArray_real_T *r947;
  emxArray_real_T *r948;
  emxArray_real_T *r949;
  emxArray_real_T *r950;
  emxArray_real_T *r951;
  emxArray_real_T *r952;
  emxArray_real_T *r953;
  emxArray_real_T *r954;
  emxArray_real_T *r955;
  emxArray_real_T *r956;
  emxArray_real_T *r957;
  emxArray_real_T *r958;
  emxArray_real_T *r959;
  emxArray_real_T *r960;
  emxArray_real_T *r961;
  emxArray_real_T *r962;
  emxArray_real_T *r963;
  emxArray_real_T *r964;
  emxInit_real_T(&Tb, 2);

  /*  extract states */
  loop_ub = X->size[1];
  i25 = Tb->size[0] * Tb->size[1];
  Tb->size[0] = 1;
  Tb->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Tb, i25, (int)sizeof(double));
  for (i25 = 0; i25 < loop_ub; i25++) {
    Tb->data[Tb->size[0] * i25] = X->data[7 + X->size[0] * i25];
  }

  emxInit_real_T(&b_X, 2);

  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  loop_ub = X->size[1];
  i25 = b_X->size[0] * b_X->size[1];
  b_X->size[0] = 1;
  b_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)b_X, i25, (int)sizeof(double));
  for (i25 = 0; i25 < loop_ub; i25++) {
    b_X->data[b_X->size[0] * i25] = X->data[X->size[0] * i25];
  }

  emxInit_real_T(&xpS, 2);
  emxInit_real_T(&r813, 2);
  rdivide(b_X, 1266.666666666667, xpS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i25 = r813->size[0] * r813->size[1];
  r813->size[0] = 1;
  r813->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r813, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&b_X);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r813->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&b, 2);
  emxInit_real_T(&r814, 2);
  power(r813, b);
  i25 = r814->size[0] * r814->size[1];
  r814->size[0] = 1;
  r814->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r814, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r813);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r814->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r815, 2);
  emxInit_real_T(&r816, 2);
  b_power(r814, r815);
  i25 = r816->size[0] * r816->size[1];
  r816->size[0] = 1;
  r816->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r816, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r814);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r816->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r817, 2);
  emxInit_real_T(&r818, 2);
  c_power(r816, r817);
  i25 = r818->size[0] * r818->size[1];
  r818->size[0] = 1;
  r818->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r818, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r816);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r818->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r819, 2);
  emxInit_real_T(&r820, 2);
  d_power(r818, r819);
  i25 = r820->size[0] * r820->size[1];
  r820->size[0] = 1;
  r820->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r820, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r818);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r820->data[i25] = 2.0 * xpS->data[i25] * 2.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r821, 2);
  emxInit_real_T(&r822, 2);
  b_rdivide(r820, r819, r821);
  i25 = r822->size[0] * r822->size[1];
  r822->size[0] = 1;
  r822->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r822, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r820);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r822->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r823, 2);
  e_power(r822, r819);
  i25 = r823->size[0] * r823->size[1];
  r823->size[0] = 1;
  r823->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r823, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r822);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r823->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r824, 2);
  emxInit_real_T(&r825, 2);
  f_power(r823, r824);
  i25 = r825->size[0] * r825->size[1];
  r825->size[0] = 1;
  r825->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r825, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r823);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r825->data[i25] = 2.0 * xpS->data[i25] * 3.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r826, 2);
  emxInit_real_T(&r827, 2);
  b_rdivide(r825, r824, r826);
  i25 = r827->size[0] * r827->size[1];
  r827->size[0] = 1;
  r827->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r827, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r825);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r827->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r828, 2);
  g_power(r827, r824);
  i25 = r828->size[0] * r828->size[1];
  r828->size[0] = 1;
  r828->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r828, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r827);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r828->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r829, 2);
  emxInit_real_T(&r830, 2);
  h_power(r828, r829);
  i25 = r830->size[0] * r830->size[1];
  r830->size[0] = 1;
  r830->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r830, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r828);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r830->data[i25] = 2.0 * xpS->data[i25] * 4.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r831, 2);
  emxInit_real_T(&r832, 2);
  b_rdivide(r830, r829, r831);
  i25 = r832->size[0] * r832->size[1];
  r832->size[0] = 1;
  r832->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r832, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r830);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r832->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r833, 2);
  i_power(r832, r829);
  i25 = r833->size[0] * r833->size[1];
  r833->size[0] = 1;
  r833->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r833, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r832);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r833->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r834, 2);
  emxInit_real_T(&r835, 2);
  j_power(r833, r834);
  i25 = r835->size[0] * r835->size[1];
  r835->size[0] = 1;
  r835->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r835, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r833);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r835->data[i25] = 2.0 * xpS->data[i25] * 5.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r836, 2);
  emxInit_real_T(&r837, 2);
  b_rdivide(r835, r834, r836);
  i25 = r837->size[0] * r837->size[1];
  r837->size[0] = 1;
  r837->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r837, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r835);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r837->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r838, 2);
  k_power(r837, r834);
  i25 = r838->size[0] * r838->size[1];
  r838->size[0] = 1;
  r838->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r838, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r837);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r838->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r839, 2);
  emxInit_real_T(&r840, 2);
  l_power(r838, r839);
  i25 = r840->size[0] * r840->size[1];
  r840->size[0] = 1;
  r840->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r840, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r838);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r840->data[i25] = 2.0 * xpS->data[i25] * 6.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r841, 2);
  emxInit_real_T(&r842, 2);
  b_rdivide(r840, r839, r841);
  i25 = r842->size[0] * r842->size[1];
  r842->size[0] = 1;
  r842->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r842, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r840);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r842->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r843, 2);
  m_power(r842, r839);
  i25 = r843->size[0] * r843->size[1];
  r843->size[0] = 1;
  r843->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r843, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r842);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r843->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r844, 2);
  emxInit_real_T(&r845, 2);
  n_power(r843, r844);
  i25 = r845->size[0] * r845->size[1];
  r845->size[0] = 1;
  r845->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r845, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r843);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r845->data[i25] = 2.0 * xpS->data[i25] * 7.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r846, 2);
  emxInit_real_T(&r847, 2);
  b_rdivide(r845, r844, r846);
  i25 = r847->size[0] * r847->size[1];
  r847->size[0] = 1;
  r847->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r847, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r845);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r847->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r848, 2);
  o_power(r847, r844);
  i25 = r848->size[0] * r848->size[1];
  r848->size[0] = 1;
  r848->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r848, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r847);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r848->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r849, 2);
  emxInit_real_T(&r850, 2);
  p_power(r848, r849);
  i25 = r850->size[0] * r850->size[1];
  r850->size[0] = 1;
  r850->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r850, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r848);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r850->data[i25] = 2.0 * xpS->data[i25] * 8.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r851, 2);
  emxInit_real_T(&r852, 2);
  b_rdivide(r850, r849, r851);
  i25 = r852->size[0] * r852->size[1];
  r852->size[0] = 1;
  r852->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r852, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r850);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r852->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r853, 2);
  q_power(r852, r849);
  i25 = r853->size[0] * r853->size[1];
  r853->size[0] = 1;
  r853->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r853, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r852);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r853->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r854, 2);
  emxInit_real_T(&r855, 2);
  r_power(r853, r854);
  i25 = r855->size[0] * r855->size[1];
  r855->size[0] = 1;
  r855->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r855, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r853);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r855->data[i25] = 2.0 * xpS->data[i25] * 9.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r856, 2);
  emxInit_real_T(&r857, 2);
  b_rdivide(r855, r854, r856);
  i25 = r857->size[0] * r857->size[1];
  r857->size[0] = 1;
  r857->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r857, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r855);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r857->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r858, 2);
  s_power(r857, r854);
  i25 = r858->size[0] * r858->size[1];
  r858->size[0] = 1;
  r858->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r858, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r857);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r858->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r859, 2);
  emxInit_real_T(&r860, 2);
  t_power(r858, r859);
  i25 = r860->size[0] * r860->size[1];
  r860->size[0] = 1;
  r860->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r860, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r858);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r860->data[i25] = 2.0 * xpS->data[i25] * 10.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r861, 2);
  emxInit_real_T(&r862, 2);
  b_rdivide(r860, r859, r861);
  i25 = r862->size[0] * r862->size[1];
  r862->size[0] = 1;
  r862->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r862, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r860);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r862->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r863, 2);
  u_power(r862, r859);
  i25 = r863->size[0] * r863->size[1];
  r863->size[0] = 1;
  r863->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r863, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r862);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r863->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r864, 2);
  emxInit_real_T(&r865, 2);
  v_power(r863, r864);
  i25 = r865->size[0] * r865->size[1];
  r865->size[0] = 1;
  r865->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r865, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r863);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r865->data[i25] = 2.0 * xpS->data[i25] * 11.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r866, 2);
  emxInit_real_T(&r867, 2);
  b_rdivide(r865, r864, r866);
  i25 = r867->size[0] * r867->size[1];
  r867->size[0] = 1;
  r867->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r867, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r865);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r867->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r868, 2);
  w_power(r867, r864);
  i25 = r868->size[0] * r868->size[1];
  r868->size[0] = 1;
  r868->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r868, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r867);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r868->data[i25] = 2.0 * xpS->data[i25] - 1.0;
  }

  emxInit_real_T(&r869, 2);
  emxInit_real_T(&r870, 2);
  x_power(r868, r869);
  i25 = r870->size[0] * r870->size[1];
  r870->size[0] = 1;
  r870->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r870, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r868);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r870->data[i25] = 2.0 * xpS->data[i25] * 12.0 * (1.0 - xpS->data[i25]);
  }

  emxInit_real_T(&r871, 2);
  emxInit_real_T(&r872, 2);
  b_rdivide(r870, r869, r871);
  i25 = r872->size[0] * r872->size[1];
  r872->size[0] = 1;
  r872->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r872, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r870);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r872->data[i25] = 1.0 - xpS->data[i25];
  }

  emxInit_real_T(&c_X, 2);
  b_rdivide(r872, xpS, r869);
  c_log(r869);

  /*  compute mole fraction at surface, negative electrode */
  loop_ub = X->size[1];
  i25 = c_X->size[0] * c_X->size[1];
  c_X->size[0] = 1;
  c_X->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)c_X, i25, (int)sizeof(double));
  emxFree_real_T(&r872);
  for (i25 = 0; i25 < loop_ub; i25++) {
    c_X->data[c_X->size[0] * i25] = X->data[3 + X->size[0] * i25];
  }

  emxInit_real_T(&xnS, 2);
  emxInit_real_T(&r873, 2);
  rdivide(c_X, 1266.666666666667, xnS);

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  i25 = r873->size[0] * r873->size[1];
  r873->size[0] = 1;
  r873->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r873, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&c_X);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r873->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&b_b, 2);
  emxInit_real_T(&r874, 2);
  power(r873, b_b);
  i25 = r874->size[0] * r874->size[1];
  r874->size[0] = 1;
  r874->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r874, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r873);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r874->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r875, 2);
  emxInit_real_T(&r876, 2);
  b_power(r874, r875);
  i25 = r876->size[0] * r876->size[1];
  r876->size[0] = 1;
  r876->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r876, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r874);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r876->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r877, 2);
  emxInit_real_T(&r878, 2);
  c_power(r876, r877);
  i25 = r878->size[0] * r878->size[1];
  r878->size[0] = 1;
  r878->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r878, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r876);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r878->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r879, 2);
  emxInit_real_T(&r880, 2);
  d_power(r878, r879);
  i25 = r880->size[0] * r880->size[1];
  r880->size[0] = 1;
  r880->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r880, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r878);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r880->data[i25] = 2.0 * xnS->data[i25] * 2.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r881, 2);
  emxInit_real_T(&r882, 2);
  b_rdivide(r880, r879, r881);
  i25 = r882->size[0] * r882->size[1];
  r882->size[0] = 1;
  r882->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r882, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r880);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r882->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r883, 2);
  e_power(r882, r879);
  i25 = r883->size[0] * r883->size[1];
  r883->size[0] = 1;
  r883->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r883, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r882);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r883->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r884, 2);
  emxInit_real_T(&r885, 2);
  f_power(r883, r884);
  i25 = r885->size[0] * r885->size[1];
  r885->size[0] = 1;
  r885->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r885, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r883);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r885->data[i25] = 2.0 * xnS->data[i25] * 3.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r886, 2);
  emxInit_real_T(&r887, 2);
  b_rdivide(r885, r884, r886);
  i25 = r887->size[0] * r887->size[1];
  r887->size[0] = 1;
  r887->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r887, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r885);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r887->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r888, 2);
  g_power(r887, r884);
  i25 = r888->size[0] * r888->size[1];
  r888->size[0] = 1;
  r888->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r888, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r887);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r888->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r889, 2);
  emxInit_real_T(&r890, 2);
  h_power(r888, r889);
  i25 = r890->size[0] * r890->size[1];
  r890->size[0] = 1;
  r890->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r890, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r888);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r890->data[i25] = 2.0 * xnS->data[i25] * 4.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r891, 2);
  emxInit_real_T(&r892, 2);
  b_rdivide(r890, r889, r891);
  i25 = r892->size[0] * r892->size[1];
  r892->size[0] = 1;
  r892->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r892, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r890);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r892->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r893, 2);
  i_power(r892, r889);
  i25 = r893->size[0] * r893->size[1];
  r893->size[0] = 1;
  r893->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r893, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r892);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r893->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r894, 2);
  emxInit_real_T(&r895, 2);
  j_power(r893, r894);
  i25 = r895->size[0] * r895->size[1];
  r895->size[0] = 1;
  r895->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r895, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r893);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r895->data[i25] = 2.0 * xnS->data[i25] * 5.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r896, 2);
  emxInit_real_T(&r897, 2);
  b_rdivide(r895, r894, r896);
  i25 = r897->size[0] * r897->size[1];
  r897->size[0] = 1;
  r897->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r897, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r895);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r897->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r898, 2);
  k_power(r897, r894);
  i25 = r898->size[0] * r898->size[1];
  r898->size[0] = 1;
  r898->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r898, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r897);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r898->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r899, 2);
  emxInit_real_T(&r900, 2);
  l_power(r898, r899);
  i25 = r900->size[0] * r900->size[1];
  r900->size[0] = 1;
  r900->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r900, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r898);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r900->data[i25] = 2.0 * xnS->data[i25] * 6.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r901, 2);
  emxInit_real_T(&r902, 2);
  b_rdivide(r900, r899, r901);
  i25 = r902->size[0] * r902->size[1];
  r902->size[0] = 1;
  r902->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r902, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r900);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r902->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r903, 2);
  m_power(r902, r899);
  i25 = r903->size[0] * r903->size[1];
  r903->size[0] = 1;
  r903->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r903, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r902);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r903->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r904, 2);
  emxInit_real_T(&r905, 2);
  n_power(r903, r904);
  i25 = r905->size[0] * r905->size[1];
  r905->size[0] = 1;
  r905->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r905, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r903);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r905->data[i25] = 2.0 * xnS->data[i25] * 7.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r906, 2);
  emxInit_real_T(&r907, 2);
  b_rdivide(r905, r904, r906);
  i25 = r907->size[0] * r907->size[1];
  r907->size[0] = 1;
  r907->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r907, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r905);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r907->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r908, 2);
  o_power(r907, r904);
  i25 = r908->size[0] * r908->size[1];
  r908->size[0] = 1;
  r908->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r908, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r907);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r908->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r909, 2);
  emxInit_real_T(&r910, 2);
  p_power(r908, r909);
  i25 = r910->size[0] * r910->size[1];
  r910->size[0] = 1;
  r910->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r910, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r908);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r910->data[i25] = 2.0 * xnS->data[i25] * 8.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r911, 2);
  emxInit_real_T(&r912, 2);
  b_rdivide(r910, r909, r911);
  i25 = r912->size[0] * r912->size[1];
  r912->size[0] = 1;
  r912->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r912, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r910);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r912->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r913, 2);
  q_power(r912, r909);
  i25 = r913->size[0] * r913->size[1];
  r913->size[0] = 1;
  r913->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r913, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r912);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r913->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r914, 2);
  emxInit_real_T(&r915, 2);
  r_power(r913, r914);
  i25 = r915->size[0] * r915->size[1];
  r915->size[0] = 1;
  r915->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r915, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r913);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r915->data[i25] = 2.0 * xnS->data[i25] * 9.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r916, 2);
  emxInit_real_T(&r917, 2);
  b_rdivide(r915, r914, r916);
  i25 = r917->size[0] * r917->size[1];
  r917->size[0] = 1;
  r917->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r917, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r915);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r917->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r918, 2);
  s_power(r917, r914);
  i25 = r918->size[0] * r918->size[1];
  r918->size[0] = 1;
  r918->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r918, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r917);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r918->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r919, 2);
  emxInit_real_T(&r920, 2);
  t_power(r918, r919);
  i25 = r920->size[0] * r920->size[1];
  r920->size[0] = 1;
  r920->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r920, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r918);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r920->data[i25] = 2.0 * xnS->data[i25] * 10.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r921, 2);
  emxInit_real_T(&r922, 2);
  b_rdivide(r920, r919, r921);
  i25 = r922->size[0] * r922->size[1];
  r922->size[0] = 1;
  r922->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r922, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r920);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r922->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r923, 2);
  u_power(r922, r919);
  i25 = r923->size[0] * r923->size[1];
  r923->size[0] = 1;
  r923->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r923, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r922);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r923->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r924, 2);
  emxInit_real_T(&r925, 2);
  v_power(r923, r924);
  i25 = r925->size[0] * r925->size[1];
  r925->size[0] = 1;
  r925->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r925, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r923);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r925->data[i25] = 2.0 * xnS->data[i25] * 11.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r926, 2);
  emxInit_real_T(&r927, 2);
  b_rdivide(r925, r924, r926);
  i25 = r927->size[0] * r927->size[1];
  r927->size[0] = 1;
  r927->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r927, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r925);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r927->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r928, 2);
  w_power(r927, r924);
  i25 = r928->size[0] * r928->size[1];
  r928->size[0] = 1;
  r928->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r928, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r927);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r928->data[i25] = 2.0 * xnS->data[i25] - 1.0;
  }

  emxInit_real_T(&r929, 2);
  emxInit_real_T(&r930, 2);
  x_power(r928, r929);
  i25 = r930->size[0] * r930->size[1];
  r930->size[0] = 1;
  r930->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r930, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r928);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r930->data[i25] = 2.0 * xnS->data[i25] * 12.0 * (1.0 - xnS->data[i25]);
  }

  emxInit_real_T(&r931, 2);
  emxInit_real_T(&r932, 2);
  b_rdivide(r930, r929, r931);
  i25 = r932->size[0] * r932->size[1];
  r932->size[0] = 1;
  r932->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r932, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r930);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r932->data[i25] = 1.0 - xnS->data[i25];
  }

  b_rdivide(r932, xnS, r929);
  c_log(r929);

  /*  voltages */
  /*  set outputs */
  i25 = Z->size[0] * Z->size[1];
  Z->size[0] = 2;
  emxEnsureCapacity((emxArray__common *)Z, i25, (int)sizeof(double));
  loop_ub = X->size[1];
  i25 = Z->size[0] * Z->size[1];
  Z->size[1] = loop_ub;
  emxEnsureCapacity((emxArray__common *)Z, i25, (int)sizeof(double));
  loop_ub = X->size[1] << 1;
  emxFree_real_T(&r932);
  for (i25 = 0; i25 < loop_ub; i25++) {
    Z->data[i25] = 0.0;
  }

  emxInit_real_T(&r933, 2);
  i25 = r933->size[0] * r933->size[1];
  r933->size[0] = 1;
  r933->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r933, i25, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  for (i25 = 0; i25 < loop_ub; i25++) {
    r933->data[i25] = 8.3144621 * Tb->data[i25];
  }

  emxInit_real_T(&r934, 2);
  emxInit_real_T(&r935, 2);
  rdivide(r933, 96487.0, r934);
  i25 = r935->size[0] * r935->size[1];
  r935->size[0] = 1;
  r935->size[1] = b->size[1];
  emxEnsureCapacity((emxArray__common *)r935, i25, (int)sizeof(double));
  loop_ub = b->size[0] * b->size[1];
  emxFree_real_T(&r933);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r935->data[i25] = -31593.7 * b->data[i25];
  }

  emxInit_real_T(&r936, 2);
  emxInit_real_T(&r937, 2);
  rdivide(r935, 96487.0, r936);
  i25 = r937->size[0] * r937->size[1];
  r937->size[0] = 1;
  r937->size[1] = xpS->size[1];
  emxEnsureCapacity((emxArray__common *)r937, i25, (int)sizeof(double));
  loop_ub = xpS->size[0] * xpS->size[1];
  emxFree_real_T(&r935);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r937->data[i25] = 2.0 * xpS->data[i25] * (1.0 - xpS->data[i25]);
  }

  emxFree_real_T(&xpS);
  emxInit_real_T(&r938, 2);
  rdivide(r937, 1.0, b);
  i25 = r938->size[0] * r938->size[1];
  r938->size[0] = 1;
  r938->size[1] = r815->size[1];
  emxEnsureCapacity((emxArray__common *)r938, i25, (int)sizeof(double));
  loop_ub = r815->size[0] * r815->size[1];
  emxFree_real_T(&r937);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r938->data[i25] = 0.106747 * (r815->data[i25] - b->data[i25]);
  }

  emxFree_real_T(&b);
  emxInit_real_T(&r939, 2);
  rdivide(r938, 96487.0, r815);
  i25 = r939->size[0] * r939->size[1];
  r939->size[0] = 1;
  r939->size[1] = r817->size[1];
  emxEnsureCapacity((emxArray__common *)r939, i25, (int)sizeof(double));
  loop_ub = r817->size[0] * r817->size[1];
  emxFree_real_T(&r938);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r939->data[i25] = 24606.4 * (r817->data[i25] - r821->data[i25]);
  }

  emxInit_real_T(&r940, 2);
  rdivide(r939, 96487.0, r817);
  i25 = r940->size[0] * r940->size[1];
  r940->size[0] = 1;
  r940->size[1] = r819->size[1];
  emxEnsureCapacity((emxArray__common *)r940, i25, (int)sizeof(double));
  loop_ub = r819->size[0] * r819->size[1];
  emxFree_real_T(&r939);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r940->data[i25] = -78561.9 * (r819->data[i25] - r826->data[i25]);
  }

  emxInit_real_T(&r941, 2);
  rdivide(r940, 96487.0, r819);
  i25 = r941->size[0] * r941->size[1];
  r941->size[0] = 1;
  r941->size[1] = r824->size[1];
  emxEnsureCapacity((emxArray__common *)r941, i25, (int)sizeof(double));
  loop_ub = r824->size[0] * r824->size[1];
  emxFree_real_T(&r940);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r941->data[i25] = 13317.9 * (r824->data[i25] - r831->data[i25]);
  }

  emxInit_real_T(&r942, 2);
  rdivide(r941, 96487.0, r821);
  i25 = r942->size[0] * r942->size[1];
  r942->size[0] = 1;
  r942->size[1] = r829->size[1];
  emxEnsureCapacity((emxArray__common *)r942, i25, (int)sizeof(double));
  loop_ub = r829->size[0] * r829->size[1];
  emxFree_real_T(&r941);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r942->data[i25] = 307387.0 * (r829->data[i25] - r836->data[i25]);
  }

  emxInit_real_T(&r943, 2);
  rdivide(r942, 96487.0, r824);
  i25 = r943->size[0] * r943->size[1];
  r943->size[0] = 1;
  r943->size[1] = r834->size[1];
  emxEnsureCapacity((emxArray__common *)r943, i25, (int)sizeof(double));
  loop_ub = r834->size[0] * r834->size[1];
  emxFree_real_T(&r942);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r943->data[i25] = 84916.1 * (r834->data[i25] - r841->data[i25]);
  }

  emxInit_real_T(&r944, 2);
  rdivide(r943, 96487.0, r826);
  i25 = r944->size[0] * r944->size[1];
  r944->size[0] = 1;
  r944->size[1] = r839->size[1];
  emxEnsureCapacity((emxArray__common *)r944, i25, (int)sizeof(double));
  loop_ub = r839->size[0] * r839->size[1];
  emxFree_real_T(&r943);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r944->data[i25] = -1.07469E+6 * (r839->data[i25] - r846->data[i25]);
  }

  emxInit_real_T(&r945, 2);
  rdivide(r944, 96487.0, r829);
  i25 = r945->size[0] * r945->size[1];
  r945->size[0] = 1;
  r945->size[1] = r844->size[1];
  emxEnsureCapacity((emxArray__common *)r945, i25, (int)sizeof(double));
  loop_ub = r844->size[0] * r844->size[1];
  emxFree_real_T(&r944);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r945->data[i25] = 2285.04 * (r844->data[i25] - r851->data[i25]);
  }

  emxInit_real_T(&r946, 2);
  rdivide(r945, 96487.0, r831);
  i25 = r946->size[0] * r946->size[1];
  r946->size[0] = 1;
  r946->size[1] = r849->size[1];
  emxEnsureCapacity((emxArray__common *)r946, i25, (int)sizeof(double));
  loop_ub = r849->size[0] * r849->size[1];
  emxFree_real_T(&r945);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r946->data[i25] = 990894.0 * (r849->data[i25] - r856->data[i25]);
  }

  emxInit_real_T(&r947, 2);
  rdivide(r946, 96487.0, r834);
  i25 = r947->size[0] * r947->size[1];
  r947->size[0] = 1;
  r947->size[1] = r854->size[1];
  emxEnsureCapacity((emxArray__common *)r947, i25, (int)sizeof(double));
  loop_ub = r854->size[0] * r854->size[1];
  emxFree_real_T(&r946);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r947->data[i25] = 283920.0 * (r854->data[i25] - r861->data[i25]);
  }

  emxInit_real_T(&r948, 2);
  rdivide(r947, 96487.0, r836);
  i25 = r948->size[0] * r948->size[1];
  r948->size[0] = 1;
  r948->size[1] = r859->size[1];
  emxEnsureCapacity((emxArray__common *)r948, i25, (int)sizeof(double));
  loop_ub = r859->size[0] * r859->size[1];
  emxFree_real_T(&r947);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r948->data[i25] = -161513.0 * (r859->data[i25] - r866->data[i25]);
  }

  emxInit_real_T(&r949, 2);
  rdivide(r948, 96487.0, r839);
  i25 = r949->size[0] * r949->size[1];
  r949->size[0] = 1;
  r949->size[1] = r864->size[1];
  emxEnsureCapacity((emxArray__common *)r949, i25, (int)sizeof(double));
  loop_ub = r864->size[0] * r864->size[1];
  emxFree_real_T(&r948);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r949->data[i25] = -469218.0 * (r864->data[i25] - r871->data[i25]);
  }

  emxInit_real_T(&r950, 2);
  rdivide(r949, 96487.0, r841);
  i25 = r950->size[0] * r950->size[1];
  r950->size[0] = 1;
  r950->size[1] = Tb->size[1];
  emxEnsureCapacity((emxArray__common *)r950, i25, (int)sizeof(double));
  loop_ub = Tb->size[0] * Tb->size[1];
  emxFree_real_T(&r949);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r950->data[i25] = 8.3144621 * Tb->data[i25];
  }

  emxInit_real_T(&r951, 2);
  rdivide(r950, 96487.0, r844);
  i25 = r951->size[0] * r951->size[1];
  r951->size[0] = 1;
  r951->size[1] = b_b->size[1];
  emxEnsureCapacity((emxArray__common *)r951, i25, (int)sizeof(double));
  loop_ub = b_b->size[0] * b_b->size[1];
  emxFree_real_T(&r950);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r951->data[i25] = 86.19 * b_b->data[i25];
  }

  emxFree_real_T(&b_b);
  emxInit_real_T(&r952, 2);
  rdivide(r951, 96487.0, r846);
  i25 = r952->size[0] * r952->size[1];
  r952->size[0] = 1;
  r952->size[1] = xnS->size[1];
  emxEnsureCapacity((emxArray__common *)r952, i25, (int)sizeof(double));
  loop_ub = xnS->size[0] * xnS->size[1];
  emxFree_real_T(&r951);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r952->data[i25] = 2.0 * xnS->data[i25] * (1.0 - xnS->data[i25]);
  }

  emxFree_real_T(&xnS);
  emxInit_real_T(&r953, 2);
  rdivide(r952, 1.0, r849);
  i25 = r953->size[0] * r953->size[1];
  r953->size[0] = 1;
  r953->size[1] = r875->size[1];
  emxEnsureCapacity((emxArray__common *)r953, i25, (int)sizeof(double));
  loop_ub = r875->size[0] * r875->size[1];
  emxFree_real_T(&r952);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r953->data[i25] = 0.0 * (r875->data[i25] - r849->data[i25]);
  }

  emxInit_real_T(&r954, 2);
  rdivide(r953, 96487.0, r849);
  i25 = r954->size[0] * r954->size[1];
  r954->size[0] = 1;
  r954->size[1] = r877->size[1];
  emxEnsureCapacity((emxArray__common *)r954, i25, (int)sizeof(double));
  loop_ub = r877->size[0] * r877->size[1];
  emxFree_real_T(&r953);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r954->data[i25] = 0.0 * (r877->data[i25] - r881->data[i25]);
  }

  emxFree_real_T(&r881);
  emxInit_real_T(&r955, 2);
  rdivide(r954, 96487.0, r851);
  i25 = r955->size[0] * r955->size[1];
  r955->size[0] = 1;
  r955->size[1] = r879->size[1];
  emxEnsureCapacity((emxArray__common *)r955, i25, (int)sizeof(double));
  loop_ub = r879->size[0] * r879->size[1];
  emxFree_real_T(&r954);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r955->data[i25] = 0.0 * (r879->data[i25] - r886->data[i25]);
  }

  emxFree_real_T(&r886);
  emxInit_real_T(&r956, 2);
  rdivide(r955, 96487.0, r854);
  i25 = r956->size[0] * r956->size[1];
  r956->size[0] = 1;
  r956->size[1] = r884->size[1];
  emxEnsureCapacity((emxArray__common *)r956, i25, (int)sizeof(double));
  loop_ub = r884->size[0] * r884->size[1];
  emxFree_real_T(&r955);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r956->data[i25] = 0.0 * (r884->data[i25] - r891->data[i25]);
  }

  emxFree_real_T(&r884);
  emxFree_real_T(&r891);
  emxInit_real_T(&r957, 2);
  rdivide(r956, 96487.0, r856);
  i25 = r957->size[0] * r957->size[1];
  r957->size[0] = 1;
  r957->size[1] = r889->size[1];
  emxEnsureCapacity((emxArray__common *)r957, i25, (int)sizeof(double));
  loop_ub = r889->size[0] * r889->size[1];
  emxFree_real_T(&r956);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r957->data[i25] = 0.0 * (r889->data[i25] - r896->data[i25]);
  }

  emxFree_real_T(&r889);
  emxFree_real_T(&r896);
  emxInit_real_T(&r958, 2);
  rdivide(r957, 96487.0, r859);
  i25 = r958->size[0] * r958->size[1];
  r958->size[0] = 1;
  r958->size[1] = r894->size[1];
  emxEnsureCapacity((emxArray__common *)r958, i25, (int)sizeof(double));
  loop_ub = r894->size[0] * r894->size[1];
  emxFree_real_T(&r957);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r958->data[i25] = 0.0 * (r894->data[i25] - r901->data[i25]);
  }

  emxFree_real_T(&r894);
  emxFree_real_T(&r901);
  emxInit_real_T(&r959, 2);
  rdivide(r958, 96487.0, r861);
  i25 = r959->size[0] * r959->size[1];
  r959->size[0] = 1;
  r959->size[1] = r899->size[1];
  emxEnsureCapacity((emxArray__common *)r959, i25, (int)sizeof(double));
  loop_ub = r899->size[0] * r899->size[1];
  emxFree_real_T(&r958);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r959->data[i25] = 0.0 * (r899->data[i25] - r906->data[i25]);
  }

  emxFree_real_T(&r899);
  emxFree_real_T(&r906);
  emxInit_real_T(&r960, 2);
  rdivide(r959, 96487.0, r864);
  i25 = r960->size[0] * r960->size[1];
  r960->size[0] = 1;
  r960->size[1] = r904->size[1];
  emxEnsureCapacity((emxArray__common *)r960, i25, (int)sizeof(double));
  loop_ub = r904->size[0] * r904->size[1];
  emxFree_real_T(&r959);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r960->data[i25] = 0.0 * (r904->data[i25] - r911->data[i25]);
  }

  emxFree_real_T(&r904);
  emxFree_real_T(&r911);
  emxInit_real_T(&r961, 2);
  rdivide(r960, 96487.0, r866);
  i25 = r961->size[0] * r961->size[1];
  r961->size[0] = 1;
  r961->size[1] = r909->size[1];
  emxEnsureCapacity((emxArray__common *)r961, i25, (int)sizeof(double));
  loop_ub = r909->size[0] * r909->size[1];
  emxFree_real_T(&r960);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r961->data[i25] = 0.0 * (r909->data[i25] - r916->data[i25]);
  }

  emxFree_real_T(&r909);
  emxFree_real_T(&r916);
  emxInit_real_T(&r962, 2);
  rdivide(r961, 96487.0, r871);
  i25 = r962->size[0] * r962->size[1];
  r962->size[0] = 1;
  r962->size[1] = r914->size[1];
  emxEnsureCapacity((emxArray__common *)r962, i25, (int)sizeof(double));
  loop_ub = r914->size[0] * r914->size[1];
  emxFree_real_T(&r961);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r962->data[i25] = 0.0 * (r914->data[i25] - r921->data[i25]);
  }

  emxFree_real_T(&r914);
  emxFree_real_T(&r921);
  emxInit_real_T(&r963, 2);
  rdivide(r962, 96487.0, r875);
  i25 = r963->size[0] * r963->size[1];
  r963->size[0] = 1;
  r963->size[1] = r919->size[1];
  emxEnsureCapacity((emxArray__common *)r963, i25, (int)sizeof(double));
  loop_ub = r919->size[0] * r919->size[1];
  emxFree_real_T(&r962);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r963->data[i25] = 0.0 * (r919->data[i25] - r926->data[i25]);
  }

  emxFree_real_T(&r919);
  emxFree_real_T(&r926);
  emxInit_real_T(&r964, 2);
  rdivide(r963, 96487.0, r877);
  i25 = r964->size[0] * r964->size[1];
  r964->size[0] = 1;
  r964->size[1] = r924->size[1];
  emxEnsureCapacity((emxArray__common *)r964, i25, (int)sizeof(double));
  loop_ub = r924->size[0] * r924->size[1];
  emxFree_real_T(&r963);
  for (i25 = 0; i25 < loop_ub; i25++) {
    r964->data[i25] = 0.0 * (r924->data[i25] - r931->data[i25]);
  }

  emxFree_real_T(&r924);
  emxFree_real_T(&r931);
  rdivide(r964, 96487.0, r879);
  loop_ub = r934->size[1];
  emxFree_real_T(&r964);
  for (i25 = 0; i25 < loop_ub; i25++) {
    Z->data[Z->size[0] * i25] = (((((((((((((((((4.03 + r934->data[r934->size[0]
      * i25] * r869->data[r869->size[0] * i25]) + r936->data[r936->size[0] * i25])
      + r815->data[r815->size[0] * i25]) + r817->data[r817->size[0] * i25]) +
      r819->data[r819->size[0] * i25]) + r821->data[r821->size[0] * i25]) +
      r824->data[r824->size[0] * i25]) + r826->data[r826->size[0] * i25]) +
      r829->data[r829->size[0] * i25]) + r831->data[r831->size[0] * i25]) +
      r834->data[r834->size[0] * i25]) + r836->data[r836->size[0] * i25]) +
      r839->data[r839->size[0] * i25]) + r841->data[r841->size[0] * i25]) -
                                   ((((((((((((((0.01 + r844->data[r844->size[0]
      * i25] * r929->data[r929->size[0] * i25]) + r846->data[r846->size[0] * i25])
      + r849->data[r849->size[0] * i25]) + r851->data[r851->size[0] * i25]) +
      r854->data[r854->size[0] * i25]) + r856->data[r856->size[0] * i25]) +
      r859->data[r859->size[0] * i25]) + r861->data[r861->size[0] * i25]) +
      r864->data[r864->size[0] * i25]) + r866->data[r866->size[0] * i25]) +
      r871->data[r871->size[0] * i25]) + r875->data[r875->size[0] * i25]) +
      r877->data[r877->size[0] * i25]) + r879->data[r879->size[0] * i25])) -
      X->data[4 + X->size[0] * i25]) - X->data[5 + X->size[0] * i25]) - X->data
      [6 + X->size[0] * i25];
  }

  emxFree_real_T(&r936);
  emxFree_real_T(&r934);
  emxFree_real_T(&r929);
  emxFree_real_T(&r879);
  emxFree_real_T(&r869);
  emxFree_real_T(&r864);
  emxFree_real_T(&r859);
  emxFree_real_T(&r854);
  emxFree_real_T(&r849);
  emxFree_real_T(&r844);
  emxFree_real_T(&r839);
  emxFree_real_T(&r834);
  emxFree_real_T(&r829);
  emxFree_real_T(&r824);
  emxFree_real_T(&r819);
  emxFree_real_T(&r877);
  emxFree_real_T(&r875);
  emxFree_real_T(&r871);
  emxFree_real_T(&r866);
  emxFree_real_T(&r861);
  emxFree_real_T(&r856);
  emxFree_real_T(&r851);
  emxFree_real_T(&r846);
  emxFree_real_T(&r841);
  emxFree_real_T(&r836);
  emxFree_real_T(&r831);
  emxFree_real_T(&r826);
  emxFree_real_T(&r821);
  emxFree_real_T(&r817);
  emxFree_real_T(&r815);
  loop_ub = Tb->size[1];
  for (i25 = 0; i25 < loop_ub; i25++) {
    Z->data[1 + Z->size[0] * i25] = Tb->data[Tb->size[0] * i25] - 273.15;
  }

  emxFree_real_T(&Tb);

  /*  convert to C */
  /*  add noise */
}

/*
 * This version of the output eqn function does not need P as an argument. It
 *  is needed for the UKF for compilation purposes due to the restrictions on
 *  the use of function handles.
 * Arguments    : const emxArray_real_T *X
 *                double Z[2]
 * Return Type  : void
 */
void c_OutputEqnUKF(const emxArray_real_T *X, double Z[2])
{
  double xpS;
  double a;
  double xnS;
  double b_a;

  /*  extract states */
  /*  extract inputs */
  /*  compute mole fraction at surface, pos electrode */
  xpS = X->data[0] / 1266.666666666667;

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  a = 2.0 * xpS - 1.0;

  /*  compute mole fraction at surface, negative electrode */
  xnS = X->data[3] / 1266.666666666667;

  /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
  b_a = 2.0 * xnS - 1.0;

  /*  voltages */
  /*  set outputs */
  Z[0] = (((((((((((((((((4.03 + 8.3144621 * X->data[7] / 96487.0 * log((1.0 -
    xpS) / xpS)) + -31593.7 * (2.0 * xpS - 1.0) / 96487.0) + 0.106747 * (a * a -
    2.0 * xpS * (1.0 - xpS)) / 96487.0) + 24606.4 * (rt_powd_snf(2.0 * xpS - 1.0,
    3.0) - 2.0 * xpS * 2.0 * (1.0 - xpS) / (1.0 / (2.0 * xpS - 1.0))) / 96487.0)
                      + -78561.9 * (rt_powd_snf(2.0 * xpS - 1.0, 4.0) - 2.0 *
    xpS * 3.0 * (1.0 - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -2.0)) / 96487.0) +
                     13317.9 * (rt_powd_snf(2.0 * xpS - 1.0, 5.0) - 2.0 * xpS *
    4.0 * (1.0 - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -3.0)) / 96487.0) +
                    307387.0 * (rt_powd_snf(2.0 * xpS - 1.0, 6.0) - 2.0 * xpS *
    5.0 * (1.0 - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -4.0)) / 96487.0) + 84916.1
                   * (rt_powd_snf(2.0 * xpS - 1.0, 7.0) - 2.0 * xpS * 6.0 * (1.0
    - xpS) / rt_powd_snf(2.0 * xpS - 1.0, -5.0)) / 96487.0) + -1.07469E+6 *
                  (rt_powd_snf(2.0 * xpS - 1.0, 8.0) - 2.0 * xpS * 7.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -6.0)) / 96487.0) + 2285.04 *
                 (rt_powd_snf(2.0 * xpS - 1.0, 9.0) - 2.0 * xpS * 8.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -7.0)) / 96487.0) + 990894.0 *
                (rt_powd_snf(2.0 * xpS - 1.0, 10.0) - 2.0 * xpS * 9.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -8.0)) / 96487.0) + 283920.0 *
               (rt_powd_snf(2.0 * xpS - 1.0, 11.0) - 2.0 * xpS * 10.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -9.0)) / 96487.0) + -161513.0 *
              (rt_powd_snf(2.0 * xpS - 1.0, 12.0) - 2.0 * xpS * 11.0 * (1.0 -
    xpS) / rt_powd_snf(2.0 * xpS - 1.0, -10.0)) / 96487.0) + -469218.0 *
             (rt_powd_snf(2.0 * xpS - 1.0, 13.0) - 2.0 * xpS * 12.0 * (1.0 - xpS)
              / rt_powd_snf(2.0 * xpS - 1.0, -11.0)) / 96487.0) -
            ((((((((((((((0.01 + 8.3144621 * X->data[7] / 96487.0 * log((1.0 -
    xnS) / xnS)) + 86.19 * (2.0 * xnS - 1.0) / 96487.0) + 0.0 * (b_a * b_a - 2.0
    * xnS * (1.0 - xnS)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 3.0) -
    2.0 * xnS * 2.0 * (1.0 - xnS) / (1.0 / (2.0 * xnS - 1.0))) / 96487.0) + 0.0 *
                      (rt_powd_snf(2.0 * xnS - 1.0, 4.0) - 2.0 * xnS * 3.0 *
                       (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -2.0)) /
                      96487.0) + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 5.0) - 2.0 *
    xnS * 4.0 * (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -3.0)) / 96487.0) +
                    0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 6.0) - 2.0 * xnS * 5.0 *
                     (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -4.0)) / 96487.0)
                   + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 7.0) - 2.0 * xnS * 6.0 *
                    (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -5.0)) / 96487.0)
                  + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 8.0) - 2.0 * xnS * 7.0 *
                   (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -6.0)) / 96487.0)
                 + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 9.0) - 2.0 * xnS * 8.0 *
                  (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -7.0)) / 96487.0) +
                0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 10.0) - 2.0 * xnS * 9.0 *
                       (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -8.0)) /
                96487.0) + 0.0 * (rt_powd_snf(2.0 * xnS - 1.0, 11.0) - 2.0 * xnS
    * 10.0 * (1.0 - xnS) / rt_powd_snf(2.0 * xnS - 1.0, -9.0)) / 96487.0) + 0.0 *
              (rt_powd_snf(2.0 * xnS - 1.0, 12.0) - 2.0 * xnS * 11.0 * (1.0 -
    xnS) / rt_powd_snf(2.0 * xnS - 1.0, -10.0)) / 96487.0) + 0.0 * (rt_powd_snf
              (2.0 * xnS - 1.0, 13.0) - 2.0 * xnS * 12.0 * (1.0 - xnS) /
              rt_powd_snf(2.0 * xnS - 1.0, -11.0)) / 96487.0)) - X->data[4]) -
          X->data[5]) - X->data[6];
  Z[1] = X->data[7] - 273.15;

  /*  convert to C */
  /*  add noise */
}

/*
 * File trailer for OutputEqnUKF.c
 *
 * [EOF]
 */
