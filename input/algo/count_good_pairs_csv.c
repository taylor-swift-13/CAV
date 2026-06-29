#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (count_good_pairs_csv_pre : list Z -> Prop) */
/*@ Extern Coq (count_good_pairs_csv_spec : list Z -> Z) */
/*@ Import Coq Require Import count_good_pairs_csv */

int count_good_pairs_csv(const char *nums)
/*@ With l n
    Require
      nums != 0 &&
      0 <= n &&
      n <= 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      count_good_pairs_csv_pre(l) &&
      CharArray::full((char *)nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == count_good_pairs_csv_spec(l) &&
      CharArray::full((char *)nums, n + 1, app(l, cons(0, nil)))
*/
{
    int values[128];
    int n = 0;
    int i = 0;

    while (1) {
        if (nums[i] == 0) {
            break;
        }

        int sign = 1;
        if (nums[i] == 45) {
            sign = -1;
            i++;
        }

        int v = 0;
        while (1) {
            if (nums[i] < 48 || nums[i] > 57) {
                break;
            }
            v = v * 10 + (nums[i] - 48);
            i++;
        }

        values[n] = sign * v;
        n++;

        if (nums[i] == 44) {
            i++;
        }
    }

    int count = 0;
    for (int a = 0; a < n; a++) {
        for (int b = a + 1; b < n; b++) {
            if (values[a] == values[b]) {
                count++;
            }
        }
    }

    return count;
}
