#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

int array_index_of_max(int n, int *a)
/*@ With l
    Require
      1 <= n &&
      Zlength(l) == n &&
      IntArray::full(a, n, l)
    Ensure
      0 <= __return &&
      __return < n &&
      (forall (j: Z), (0 <= j && j < n) => l[j] <= l[__return]) &&
      (forall (j: Z), (0 <= j && j < __return) => l[j] < l[__return]) &&
      IntArray::full(a, n, l)
*/
{
    int idx = 0;
    int i = 1;

    while (i < n) {
        if (a[i] > a[idx]) {
            idx = i;
        }
        i++;
    }

    return idx;
}
