/*
 * File: asinh.c
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
#include "asinh.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Arguments    : emxArray_real_T *x
 * Return Type  : void
 */
void b_asinh(emxArray_real_T *x)
{
  int i31;
  int k;
  double z;
  boolean_T xneg;
  double t;
  i31 = x->size[1];
  for (k = 0; k < i31; k++) {
    z = x->data[k];
    xneg = (x->data[k] < 0.0);
    if (xneg) {
      z = -x->data[k];
    }

    if (z >= 2.68435456E+8) {
      z = log(z) + 0.69314718055994529;
    } else if (z > 2.0) {
      z = log(2.0 * z + 1.0 / (sqrt(z * z + 1.0) + z));
    } else {
      t = z * z;
      z += t / (1.0 + sqrt(1.0 + t));
      t = fabs(z);
      if ((t > 4.503599627370496E+15) || (!((!rtIsInf(z)) && (!rtIsNaN(z))))) {
        z = log(1.0 + z);
      } else if (t < 2.2204460492503131E-16) {
      } else {
        z = log(1.0 + z) * (z / ((1.0 + z) - 1.0));
      }
    }

    if (xneg) {
      z = -z;
    }

    x->data[k] = z;
  }
}

/*
 * File trailer for asinh.c
 *
 * [EOF]
 */
