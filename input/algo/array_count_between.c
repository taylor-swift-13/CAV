#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (array_count_between_spec : list Z -> Z -> Z -> Z) */
/*@ Import Coq Require Import array_count_between */

int array_count_between(int n, int *a, int lo, int hi)
/*@ With l
    Require
      0 <= n &&
      lo <= hi &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_between_spec(l, lo@pre, hi@pre) &&
      IntArray::full(a, n, l)
*/
{
    int i = 0;
    int count = 0;

    while (i < n) {
        if (a[i] >= lo && a[i] <= hi) {
            count++;
        }
        i++;
    }

    return count;
}
