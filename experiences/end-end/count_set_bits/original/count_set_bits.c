#include "../verification_stdlib.h"

/*@ Extern Coq (count_set_bits_z : Z -> Z) */
/*@ Import Coq Require Import count_set_bits */

int count_set_bits(int n)
/*@ Require
      0 <= n &&
      n <= 2147483647 &&
      emp
    Ensure
      0 <= __return &&
      __return == count_set_bits_z(n@pre) &&
      emp
*/
{
    int count = 0;
    while (n > 0) {
        if (n % 2 == 1) {
            count++;
        }
        n /= 2;
    }
    return count;
}
