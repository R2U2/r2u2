/*
 * File: colon.c
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
#include "colon.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Arguments    : int b
 *                int y_data[]
 *                int y_size[2]
 * Return Type  : void
 */
void eml_signed_integer_colon(int b, int y_data[], int y_size[2])
{
  int yk;
  int k;
  y_size[0] = 1;
  y_size[1] = b;
  y_data[0] = 1;
  yk = 1;
  k = 2;
  while (k <= b) {
    yk++;
    y_data[1] = yk;
    k = 3;
  }
}

/*
 * File trailer for colon.c
 *
 * [EOF]
 */
