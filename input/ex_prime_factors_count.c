#include "../verification_stdlib.h"

/*@ Extern Coq (ex_prime_factors_count_spec : Z -> Z) */
/*@ Import Coq Require Import ex_prime_factors_count */

int ex_prime_factors_count(int n)
/*@ Require
      1 <= n &&
      n <= 2147483647 &&
      emp
    Ensure
      0 <= __return &&
      __return == ex_prime_factors_count_spec(n@pre) &&
      emp
*/
{
    int count = 0;
    int d;

    for (d = 2; d <= n / d; d++) {
        while (n % d == 0) {
            count++;
            n /= d;
        }
    }

    if (n > 1) {
        count++;
    }

    return count;
}
