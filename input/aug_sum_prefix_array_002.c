#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (aug_sum_prefix_array_002_pre : list Z -> Prop) */
/*@ Extern Coq (aug_sum_prefix_array_002_spec : list Z -> Z) */
/*@ Import Coq Require Import aug_sum_prefix_array_002 */

int aug_sum_prefix_array_002(char *nums)
/*@ With l n
    Require
      0 <= n &&
      n < 2147483647 &&
      Zlength(l) == n &&
      aug_sum_prefix_array_002_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == aug_sum_prefix_array_002_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
    int values[64];
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
        while (nums[i] >= 48 && nums[i] <= 57) {
            v = v * 10 + (nums[i] - 48);
            i++;
        }

        values[n] = sign * v;
        n++;

        if (nums[i] == 44) {
            i++;
        }
    }

    int sum = 0;
    int stop = n < 2 ? n : 2;

    for (int j = 0; j < stop; j++) {
        sum += values[j];
    }

    return sum;
}
