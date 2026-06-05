#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (product : list Z -> Z) */
/*@ Import Coq Require Import array_product_small */

int array_product_small(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      (forall (k: Z),
        (0 <= k && k <= n) =>
        (-2147483648 <= product(sublist(0, k, l)) &&
         product(sublist(0, k, l)) <= 2147483647)) &&
      IntArray::full(a, n, l)
    Ensure
      __return == product(l) && IntArray::full(a, n, l)
*/
{
    int i;
    int ret = 1;

    for (i = 0; i < n; i++) {
        ret *= a[i];
    }

    return ret;
}
