#include "verification_stdlib.h"

int is_even(int n)
/*@ Require emp
    Ensure (n@pre % 2 == 0 => __return == 1) &&
           (n@pre % 2 != 0 => __return == 0) && emp
*/
{
    return n % 2 == 0;
}
