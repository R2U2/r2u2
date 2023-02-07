/*
 * File: getInitialBatteryState.c
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
#include "power.h"
#include "BHM_rtwutil.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Determine initial state based on initial voltage, current, and temperature.
 *  Assumes that close to steady-state, ie, only voltage drop is due to Ro.
 *  Also, no concentration gradient, so bulk and surface concentrations are
 *  the same. This initialization is only meant to be used when the battery
 *  is at steady-state, with I=0, or if I~=0, then only voltage drop is due
 *  to Vo and a concentration gradient has not developed yet.
 * Arguments    : double I
 *                double V
 *                double T
 *                double x0[8]
 * Return Type  : void
 */
void getInitialBatteryState(double I, double V, double T, double x0[8])
{
  double Vo;
  double nominalV;
  int xp;
  boolean_T exitg1;
  double xpo;
  double qpS0;
  double a;
  double SOC;
  double Vsn;
  double Vsp;

  /*  Update: Still assume no concentration gradient, but consider also */
  /*  contributions from Vsn and Vsp. For known SOC, have a mapping to Rsn and */
  /*  Rsp (given current can compute Vsn and Vsp). So now "nominalV" below is */
  /*  equilibrium V minus Vsn minus Vsp. */
  /*  Here are paramters of polynomial functions mapping SOC to Rsn, Rsp */
  /*  Psn = [ -6.7322   23.3704  -32.8486   24.0191   -9.7965    2.2450   -0.2898    0.0341]; */
  /*  Psp = [-0.0000    0.0005    0.0003    0.0015]; */
  /*  convert temperature given in C to K */
  T += 273.15;

  /*  load battery parameters */
  /*  compute Vo contribution */
  Vo = I * 0.117215;

  /*  Since at steady-state, assumption is concentrations for surface and bulk */
  /*  volumes are the same. So using expresson for open-circuit potential, can */
  /*  compute what qS needs to be to obtain the given V. The V we observe is */
  /*  this V minus Vo. Because we do not have an analytical expression for the */
  /*  inverse of the function computing V from mole fractions, we reconstruct */
  /*  the OCP curve as a function of mole fraction, looping through to find the */
  /*  mole fractions associated with our observed voltage */
  nominalV = V + Vo;
  xp = 0;
  exitg1 = false;
  while ((!exitg1) && (xp < 6001)) {
    xpo = 0.4 + (double)xp * 0.0001;

    /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
    qpS0 = 2.0 * xpo - 1.0;

    /*  equilibrium potential at surface, pos electrode (Nernst with Redlich-Kister) */
    a = 2.0 * (1.0 - xpo) - 1.0;
    SOC = (1.0 - xpo) * 12666.666666666668 / 7600.0;
    Vsn = I * (((((((-5.7269 * rt_powd_snf(SOC, 7.0) + 19.7663 * rt_powd_snf(SOC,
      6.0)) + -27.6466 * rt_powd_snf(SOC, 5.0)) + 20.1339 * rt_powd_snf(SOC, 4.0))
                  + -8.1881 * rt_powd_snf(SOC, 3.0)) + 1.8756 * (SOC * SOC)) +
                -0.2441 * SOC) + 0.0309);
    Vsp = I * (((-0.0001 * rt_powd_snf(SOC, 3.0) + 0.0006 * (SOC * SOC)) +
                0.0002 * SOC) + 0.0015);

    /*  check if nominalV matches Ve, if so, we have our xp,xn */
    if (((((((((((((((((4.03 + 8.3144621 * T / 96487.0 * log((1.0 - xpo) / xpo))
                       + -31593.7 * (2.0 * xpo - 1.0) / 96487.0) + 0.106747 *
                      (qpS0 * qpS0 - 2.0 * xpo * (1.0 - xpo)) / 96487.0) +
                     24606.4 * (rt_powd_snf(2.0 * xpo - 1.0, 3.0) - 2.0 * xpo *
        2.0 * (1.0 - xpo) / (1.0 / (2.0 * xpo - 1.0))) / 96487.0) + -78561.9 *
                    (rt_powd_snf(2.0 * xpo - 1.0, 4.0) - 2.0 * xpo * 3.0 * (1.0
        - xpo) / rt_powd_snf(2.0 * xpo - 1.0, -2.0)) / 96487.0) + 13317.9 *
                   (rt_powd_snf(2.0 * xpo - 1.0, 5.0) - 2.0 * xpo * 4.0 * (1.0 -
      xpo) / rt_powd_snf(2.0 * xpo - 1.0, -3.0)) / 96487.0) + 307387.0 *
                  (rt_powd_snf(2.0 * xpo - 1.0, 6.0) - 2.0 * xpo * 5.0 * (1.0 -
        xpo) / rt_powd_snf(2.0 * xpo - 1.0, -4.0)) / 96487.0) + 84916.1 *
                 (rt_powd_snf(2.0 * xpo - 1.0, 7.0) - 2.0 * xpo * 6.0 * (1.0 -
        xpo) / rt_powd_snf(2.0 * xpo - 1.0, -5.0)) / 96487.0) + -1.07469E+6 *
                (rt_powd_snf(2.0 * xpo - 1.0, 8.0) - 2.0 * xpo * 7.0 * (1.0 -
                  xpo) / rt_powd_snf(2.0 * xpo - 1.0, -6.0)) / 96487.0) +
               2285.04 * (rt_powd_snf(2.0 * xpo - 1.0, 9.0) - 2.0 * xpo * 8.0 *
                          (1.0 - xpo) / rt_powd_snf(2.0 * xpo - 1.0, -7.0)) /
               96487.0) + 990894.0 * (rt_powd_snf(2.0 * xpo - 1.0, 10.0) - 2.0 *
               xpo * 9.0 * (1.0 - xpo) / rt_powd_snf(2.0 * xpo - 1.0, -8.0)) /
              96487.0) + 283920.0 * (rt_powd_snf(2.0 * xpo - 1.0, 11.0) - 2.0 *
              xpo * 10.0 * (1.0 - xpo) / rt_powd_snf(2.0 * xpo - 1.0, -9.0)) /
             96487.0) + -161513.0 * (rt_powd_snf(2.0 * xpo - 1.0, 12.0) - 2.0 *
             xpo * 11.0 * (1.0 - xpo) / rt_powd_snf(2.0 * xpo - 1.0, -10.0)) /
            96487.0) + -469218.0 * (rt_powd_snf(2.0 * xpo - 1.0, 13.0) - 2.0 *
            xpo * 12.0 * (1.0 - xpo) / rt_powd_snf(2.0 * xpo - 1.0, -11.0)) /
           96487.0) - ((((((((((((((0.01 + 8.3144621 * T / 96487.0 * log((1.0 -
                          (1.0 - xpo)) / (1.0 - xpo))) + 86.19 * (2.0 * (1.0 -
        xpo) - 1.0) / 96487.0) + 0.0 * (a * a - 2.0 * (1.0 - xpo) * (1.0 - (1.0
        - xpo))) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, 3.0) -
      2.0 * (1.0 - xpo) * 2.0 * (1.0 - (1.0 - xpo)) / (1.0 / (2.0 * (1.0 - xpo)
        - 1.0))) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, 4.0) -
      2.0 * (1.0 - xpo) * 3.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf(2.0 * (1.0 -
        xpo) - 1.0, -2.0)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * (1.0 - xpo) -
        1.0, 5.0) - 2.0 * (1.0 - xpo) * 4.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf
        (2.0 * (1.0 - xpo) - 1.0, -3.0)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 *
        (1.0 - xpo) - 1.0, 6.0) - 2.0 * (1.0 - xpo) * 5.0 * (1.0 - (1.0 - xpo)) /
      rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, -4.0)) / 96487.0) + 0.0 *
                 (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, 7.0) - 2.0 * (1.0 - xpo) *
                  6.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf(2.0 * (1.0 - xpo) -
        1.0, -5.0)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, 8.0)
      - 2.0 * (1.0 - xpo) * 7.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf(2.0 * (1.0 -
      xpo) - 1.0, -6.0)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0,
      9.0) - 2.0 * (1.0 - xpo) * 8.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf(2.0 *
                 (1.0 - xpo) - 1.0, -7.0)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 *
                (1.0 - xpo) - 1.0, 10.0) - 2.0 * (1.0 - xpo) * 9.0 * (1.0 - (1.0
      - xpo)) / rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, -8.0)) / 96487.0) + 0.0 *
                         (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, 11.0) - 2.0 *
                          (1.0 - xpo) * 10.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf
                          (2.0 * (1.0 - xpo) - 1.0, -9.0)) / 96487.0) + 0.0 *
                        (rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, 12.0) - 2.0 * (1.0
              - xpo) * 11.0 * (1.0 - (1.0 - xpo)) / rt_powd_snf(2.0 * (1.0 - xpo)
              - 1.0, -10.0)) / 96487.0) + 0.0 * (rt_powd_snf(2.0 * (1.0 - xpo) -
             1.0, 13.0) - 2.0 * (1.0 - xpo) * 12.0 * (1.0 - (1.0 - xpo)) /
            rt_powd_snf(2.0 * (1.0 - xpo) - 1.0, -11.0)) / 96487.0)) - Vsn) -
        Vsp <= nominalV) {
      SOC = 1.0 - xpo;
      exitg1 = true;
    } else {
      xpo = 0.4;
      SOC = 0.6;
      xp++;
    }
  }

  /*  Determine what qS must be for this mole fraction */
  qpS0 = 12666.666666666668 * xpo * 2.0000000000000003E-6 / 2.0E-5;
  SOC = 12666.666666666668 * SOC * 2.0000000000000003E-6 / 2.0E-5;

  /*  Determine qB given that concentrations must be equal */
  /*  set x0 */
  x0[0] = qpS0;
  x0[1] = qpS0 * 1.8E-5 / 2.0000000000000003E-6;
  x0[2] = SOC * 1.8E-5 / 2.0000000000000003E-6;
  x0[3] = SOC;
  x0[4] = Vo;
  x0[5] = Vsn;
  x0[6] = Vsp;
  x0[7] = T;
}

/*
 * File trailer for getInitialBatteryState.c
 *
 * [EOF]
 */
