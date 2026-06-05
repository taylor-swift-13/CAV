#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (array_sum_nonnegative_spec : list Z -> Z) */
/*@ Import Coq Require Import array_sum_nonnegative */

int array_sum_nonnegative(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      0 <= array_sum_nonnegative_spec(l) &&
      array_sum_nonnegative_spec(l) <= 2147483647 &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_sum_nonnegative_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int sum = 0;
    for (int i = 0; i < n; i++) {
        if (a[i] >= 0) {
            sum += a[i];
        }
    }
    return sum;
}
