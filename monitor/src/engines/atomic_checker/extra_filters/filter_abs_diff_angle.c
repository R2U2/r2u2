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
#include "filter_abs_diff_angle.h"

//------------------------------------------------------------
//	input new data x to filter; execute filter and populate
//	output buffer
//------------------------------------------------------------
r2u2_float abs_diff_angle(r2u2_float a1, r2u2_float a2){
  if (a1 < 0) a1 = a1 + 360.0;
  if (a2 < 0) a2 = a2 + 360.0;
  r2u2_float d = (r2u2_float) (a1 > a2 ? a1 - a2 : a2 - a1);
  r2u2_float c = 360.0 - d;
  r2u2_float mn = d < c ? d : c;
  return mn;
}
