#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (contains_duplicate_csv_pre : list Z -> Prop) */
/*@ Extern Coq (contains_duplicate_csv_spec : list Z -> Z) */
/*@ Import Coq Require Import contains_duplicate_csv */

int contains_duplicate_csv(char *nums)
/*@ With l n
    Require
      nums != 0 &&
      0 <= n &&
      n <= 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      contains_duplicate_csv_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == contains_duplicate_csv_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
    int values[64];
    int n = 0;
    int i = 0;

    while (1) {
        if (nums[i] == 0) break;

        int sign = 1;
        if (nums[i] == 45) {
            sign = -1;
            i++;
        }

        int v = 0;
        while (1) {
            if (nums[i] < 48 || nums[i] > 57) break;
            v = v * 10 + (nums[i] - 48);
            i++;
        }

        values[n] = sign * v;
        n++;

        if (nums[i] == 44) i++;
    }

    for (int a = 0; a < n; a++) {
        for (int b = a + 1; b < n; b++) {
            if (values[a] == values[b]) return 1;
        }
    }

    return 0;
}
