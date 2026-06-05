#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (sum_abs: list Z -> Z) */
/*@ Import Coq Require Import array_sum_abs */

int array_sum_abs(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      (forall (i: Z), (0 <= i && i < n) => (-2147483647 <= l[i])) &&
      0 <= sum_abs(l) && sum_abs(l) <= 2147483647 &&
      IntArray::full(a, n, l)
    Ensure
      __return == sum_abs(l) && IntArray::full(a, n, l)
*/
{
    int i = 0;
    int sum = 0;
    while (i < n) {
        int v = a[i];
        if (v < 0) {
            v = -v;
        }
        sum += v;
        i++;
    }
    return sum;
}
