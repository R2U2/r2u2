/*
 * File: fileManager.c
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
#include "fileManager.h"
#include <stdio.h>

/* Function Definitions */

/*
 * Arguments    : FILE * *f
 *                boolean_T *a
 * Return Type  : void
 */
void fileManager(FILE * *f, boolean_T *a)
{
  *f = stdout;
  *a = true;
}

/*
 * File trailer for fileManager.c
 *
 * [EOF]
 */
