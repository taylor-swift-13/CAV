#include "verification_stdlib.h"

int while_i_lt_5()
/*@ Require
      emp
    Ensure
      __return == 5 &&
      emp
*/
{
    int i = 0;
    /*@ Inv
          0 <= i && i <= 5 &&
          emp
    */
    while (i < 5)
    {
        i++;
    }
    return i;
}
