#include "../verification_stdlib.h"

int ex_darts_score(int x, int y)
/*@ Require
      -46340 <= x && x <= 46340 &&
      -46340 <= y && y <= 46340 &&
      x * x + y * y <= 2147483647 &&
      emp
    Ensure
      (x@pre * x@pre + y@pre * y@pre <= 1   => __return == 10) &&
      (1 < x@pre * x@pre + y@pre * y@pre &&
       x@pre * x@pre + y@pre * y@pre <= 25  => __return == 5) &&
      (25 < x@pre * x@pre + y@pre * y@pre &&
       x@pre * x@pre + y@pre * y@pre <= 100 => __return == 1) &&
      (100 < x@pre * x@pre + y@pre * y@pre  => __return == 0) &&
      emp
*/
{
    int d = x * x + y * y;
    if (d <= 1) {
        return 10;
    }
    if (d <= 25) {
        return 5;
    }
    if (d <= 100) {
        return 1;
    }
    return 0;
}
