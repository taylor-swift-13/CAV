#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (array_min_csv_pre : list Z -> Prop) */
/*@ Extern Coq (array_min_csv_spec : list Z -> Z) */
/*@ Import Coq Require Import array_min_csv */

int array_min_csv(char *nums)
/*@ With l n
    Require
      0 <= n &&
      n <= 767 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      array_min_csv_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == array_min_csv_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int sign = 1;
    if (nums[i] == 45) {
        sign = -1;
        i++;
    }
    int best = 0;
    while (1) {
        if (nums[i] < 48 || nums[i] > 57) break;
        best = best * 10 + (nums[i] - 48);
        i++;
    }
    best = best * sign;
    if (nums[i] == 44) i++;
    while (1) {
        if (nums[i] == 0) break;
        sign = 1;
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
        v = v * sign;
        if (v < best) best = v;
        if (nums[i] == 44) i++;
    }
    return best;
}
