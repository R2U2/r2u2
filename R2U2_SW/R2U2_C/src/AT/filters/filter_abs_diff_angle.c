/*=======================================================================================
** File Name: filter_abs_diff_angle.c
**
** Title: absolute value of difference of angles (in deg)
**
** $Author:  T. Pressburger, J. Schumann
** $Revision: $
** $Date:   2016
**
** Purpose: filter for R2U2/AT
**
** Functions Defined:
** abs_angle_diff returns the minimum angle between the two given angles.
** The input angles are within (-360 .. 360).
** For example, the minimum angle between -5 and 5 is 10, as is the
** minimum angle between 5 and 355. The result is always non-negative.
**
**
** Limitations, Assumptions, External Events, and Notes:
**
** Modification History:
**  Date | Author | Description
**  ---------------------------
**
**=====================================================================================*/

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include "filter_abs_diff_angle.h"

//------------------------------------------------------------
//	input new data x to filter; execute filter and populate
//	output buffer
//------------------------------------------------------------
double abs_diff_angle(double a1, double a2){
  if (a1 < 0) a1 = a1 + 360.0;
  if (a2 < 0) a2 = a2 + 360.0;
  double d = (double)fabs(a1 - a2);
  double c = 360.0 - d;
  double mn = d < c ? d : c;
  return mn;
}
