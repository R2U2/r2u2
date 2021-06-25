/*
 * File: fprintf.c
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
#include "fprintf.h"
#include "fileManager.h"
#include <stdio.h>

/* Function Declarations */
static double c_fprintf(double varargin_1);

/* Function Definitions */

/*
 * Arguments    : double varargin_1
 * Return Type  : double
 */
static double c_fprintf(double varargin_1)
{
  int nbytesint;
  FILE * b_NULL;
  boolean_T autoflush;
  FILE * filestar;
  static const char cfmt[10] = { 'T', 'i', 'm', 'e', ':', ' ', '%', 'g', '\x0a',
    '\x00' };

  nbytesint = 0;
  b_NULL = NULL;
  fileManager(&filestar, &autoflush);
  if (filestar == b_NULL) {
  } else {
    nbytesint = fprintf(filestar, cfmt, varargin_1);
    fflush(filestar);
  }

  return nbytesint;
}

/*
 * Arguments    : double formatSpec
 * Return Type  : void
 */
void b_fprintf(double formatSpec)
{
  c_fprintf(formatSpec);
}

/*
 * File trailer for fprintf.c
 *
 * [EOF]
 */
