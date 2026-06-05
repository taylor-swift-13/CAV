#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void array_copy_even(int n, int *a, int *out)
/*@ With la lo
    Require
      0 <= n &&
      Zlength(la) == n &&
      Zlength(lo) == n &&
      (((a == out) &&
        la == lo &&
        IntArray::full(a, n, la)) ||
       ((a != out) &&
        IntArray::full(a, n, la) *
        IntArray::full(out, n, lo)))
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((la[i] % 2 == 0 => lr[i] == la[i]) &&
           (la[i] % 2 != 0 => lr[i] == 0))) &&
        (((a == out) &&
          IntArray::full(a, n, lr)) ||
         ((a != out) &&
          IntArray::full(a, n, la) *
          IntArray::full(out, n, lr)))
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
