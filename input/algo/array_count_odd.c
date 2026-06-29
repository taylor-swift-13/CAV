#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (array_count_odd_spec : list Z -> Z) */
/*@ Import Coq Require Import array_count_odd */

int array_count_odd(int n, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      __return == array_count_odd_spec(l) &&
      IntArray::full(a, n, l)
*/
{
    int i = 0;
    int count = 0;

    while (i < n) {
        if (a[i] % 2 != 0) {
            count++;
        }
        i++;
    }

    return count;
}
