#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (aug_sum_prefix_stream_002_pre : list Z -> Prop) */
/*@ Extern Coq (aug_sum_prefix_stream_002_spec : list Z -> Z) */
/*@ Import Coq Require Import aug_sum_prefix_stream_002 */

int aug_sum_prefix_stream_002(char *nums)
/*@ With l n
    Require
      0 <= n &&
      n < 2147483647 &&
      Zlength(l) == n &&
      aug_sum_prefix_stream_002_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == aug_sum_prefix_stream_002_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
    int idx = 0;
    int sum = 0;
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

        if (idx < 2) {
            sum += sign * v;
        }
        idx++;

        if (nums[i] == 44) {
            i++;
        }
    }

    return sum;
}
