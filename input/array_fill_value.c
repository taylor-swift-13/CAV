#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../int_array_def.h"

void array_fill_value(int n, int k, int *a)
/*@ With l
    Require
      0 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z), (0 <= i && i < n) => lr[i] == k) &&
        IntArray::full(a, n, lr)
*/
{
    int i = 0;
    while (i < n) {
        a[i] = k;
        i++;
    }
}
