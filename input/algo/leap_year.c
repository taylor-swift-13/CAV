#include "verification_stdlib.h"

int leap_year(int year)
/*@ Require
      1 <= year && emp
    Ensure
      (year@pre % 400 == 0 => __return == 1) &&
      (year@pre % 100 == 0 && year@pre % 400 != 0 => __return == 0) &&
      (year@pre % 4 == 0 && year@pre % 100 != 0 => __return == 1) &&
      (year@pre % 4 != 0 => __return == 0) &&
      emp
*/
{
    if (year % 400 == 0) return 1;
    if (year % 100 == 0) return 0;
    return year % 4 == 0;
}
