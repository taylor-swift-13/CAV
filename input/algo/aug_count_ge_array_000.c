#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (aug_count_ge_array_000_pre : list Z -> Prop) */
/*@ Extern Coq (aug_count_ge_array_000_spec : list Z -> Z) */
/*@ Import Coq Require Import aug_count_ge_array_000 */

int aug_count_ge_array_000(char *nums)
/*@ With l n
    Require
      0 <= n &&
      n < 2147483647 &&
      aug_count_ge_array_000_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == aug_count_ge_array_000_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int count = 0;

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
        while (nums[i] >= 48 && nums[i] <= 57) {
            v = v * 10 + (nums[i] - 48);
            i++;
        }

        if (sign * v >= -8) {
            count++;
        }

        if (nums[i] == 44) {
            i++;
        }
    }

    return count;
}
