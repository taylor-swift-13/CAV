#include "verification_stdlib.h"

/*@ Extern Coq (digit_product_z : Z -> Z) */
/*@ Extern Coq (digit_product_pre_z : Z -> Prop) */
/*@ Import Coq Require Import digit_product */

int digit_product(int n)
/*@ Require
      0 <= n &&
      digit_product_pre_z(n) && emp
    Ensure
      __return == digit_product_z(n@pre) && emp
*/
{
    if (n == 0) {
        return 0;
    }

    int product = 1;

    while (n > 0) {
        product *= n % 10;
        n /= 10;
    }

    return product;
}
