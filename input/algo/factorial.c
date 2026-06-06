#include "verification_stdlib.h"

/*@ Extern Coq (factorial_model: Z -> Z) */

int factorial(int n)
/*@ Require
      0 <= n && n <= 10 && emp
    Ensure
      __return == factorial_model(n@pre) && emp
*/
{
    int i;
    int res = 1;

    for (i = 1; i <= n; ++i) {
        res = res * i;
    }

    return res;
}
