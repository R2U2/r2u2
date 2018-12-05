// HdgAchieved = let d = abs(currHdg - goalHdg) in min(d, 360 - d) < tolerance

#include <math.h>

/* abs_angle_diff returns the minimum angle between the given angles.
 * For example, the minimum angle between 355 and 5 is 10.
 */
double abs_angle_diff(double a1, double a2){
  double d = fabs(a1 - a2);
  double c = 360.0 - d;
  double mn = d < c ? d : c;
  return mn;
}
