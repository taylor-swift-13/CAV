#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (array_is_sorted_csv_pre : list Z -> Prop) */
/*@ Extern Coq (array_is_sorted_csv_spec : list Z -> Z) */
/*@ Import Coq Require Import array_is_sorted_csv */

int array_is_sorted_csv(char *nums)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      array_is_sorted_csv_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == array_is_sorted_csv_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
    if (nums[0] == 0) return 1;
    int i = 0;
    int sign = 1;
    if (nums[i] == 45) { sign = -1; i++; }
    int prev = 0;
    while (nums[i] >= 48 && nums[i] <= 57) { prev = prev * 10 + (nums[i] - 48); i++; }
    prev *= sign;
    if (nums[i] == 44) i++;
    while (1) {
        if (nums[i] == 0) break;
        sign = 1;
        if (nums[i] == 45) { sign = -1; i++; }
        int v = 0;
        while (nums[i] >= 48 && nums[i] <= 57) { v = v * 10 + (nums[i] - 48); i++; }
        v *= sign;
        if (v < prev) return 0;
        prev = v;
        if (nums[i] == 44) i++;
    }
    return 1;
}
