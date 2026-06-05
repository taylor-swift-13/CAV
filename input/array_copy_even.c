#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

/*@ Extern Coq (array_copy_even_region_spec : Z -> Z -> Z -> list Z -> list Z) */
/*@ Import Coq Require Import array_copy_even */

void array_copy_even(int n, int *a, int *out)
/*@ With mode d la lo l
    Require
      0 <= n &&
      (
        (mode == 0 &&
         Zlength(la) == n &&
         Zlength(lo) == n &&
         IntArray::full(a, n, la) *
         IntArray::full(out, n, lo)) ||
        (mode == 1 &&
         a == out &&
         Zlength(l) == n &&
         IntArray::full(a, n, l)) ||
        (mode == 2 &&
         0 < d && d < n &&
         out == a + d * sizeof(int) &&
         Zlength(l) == n + d &&
         IntArray::full(a, n + d, l)) ||
        (mode == 3 &&
         0 < d && d < n &&
         a == out + d * sizeof(int) &&
         Zlength(l) == n + d &&
         IntArray::full(out, n + d, l))
      )
    Ensure
      (mode == 0 &&
       IntArray::full(a, n, la) *
       IntArray::full(out, n, array_copy_even_region_spec(0, 0, n, la))) ||
      (mode == 1 &&
       IntArray::full(a, n, array_copy_even_region_spec(0, 0, n, l))) ||
      (mode == 2 &&
       IntArray::full(a, n + d, array_copy_even_region_spec(0, d, n, l))) ||
      (mode == 3 &&
       IntArray::full(out, n + d, array_copy_even_region_spec(d, 0, n, l)))
*/
{
    int i = 0;

    while (i < n) {
        if (a[i] % 2 == 0) {
            out[i] = a[i];
        } else {
            out[i] = 0;
        }
        i++;
    }
}
