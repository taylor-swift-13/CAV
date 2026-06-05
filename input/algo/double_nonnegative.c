#include "verification_stdlib.h"

int double_nonnegative(int n)
/*@ Require
      0 <= n &&
      n <= 1073741823 &&
      emp
    Ensure
      __return == n@pre + n@pre &&
      0 <= __return &&
      emp
*/
{
    return n + n;
}
