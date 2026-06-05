#include "verification_stdlib.h"

int last_digit(int n)
/*@ Require
      0 <= n &&
      emp
    Ensure
      __return == n@pre % 10 &&
      emp
*/
{
    return n % 10;
}
