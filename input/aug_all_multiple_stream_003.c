#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (aug_all_multiple_stream_003_pre : list Z -> Prop) */
/*@ Extern Coq (aug_all_multiple_stream_003_spec : list Z -> Z) */
/*@ Import Coq Require Import aug_all_multiple_stream_003 */

int aug_all_multiple_stream_003(char *nums)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      aug_all_multiple_stream_003_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == aug_all_multiple_stream_003_spec(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
*/
{
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

        if ((sign * v) % 5 != 0) {
            return 0;
        }

        if (nums[i] == 44) {
            i++;
        }
    }

    return 1;
}
