#include "../verification_stdlib.h"

/*@ Extern Coq (power_nonnegative_z: Z -> Z -> Z) */
/*@ Import Coq Require Import power_nonnegative */

int ex_grains_square_value(int square)
/*@ Require
      1 <= square &&
      (forall (k: Z), (0 <= k && k <= square - 1) =>
        (-2147483648 <= power_nonnegative_z(2, k) &&
         power_nonnegative_z(2, k) <= 2147483647)) &&
      emp
    Ensure
      __return == power_nonnegative_z(2, square@pre - 1) &&
      emp
*/
{
    int value = 1;
    int i;

    for (i = 1; i < square; i++) {
        value *= 2;
    }

    return value;
}
