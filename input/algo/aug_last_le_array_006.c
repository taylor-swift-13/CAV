#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (aug_last_le_array_006_pre : list Z -> Prop) */
/*@ Extern Coq (aug_last_le_array_006_spec : list Z -> Z) */
/*@ Import Coq Require Import aug_last_le_array_006 */

int aug_last_le_array_006(char *nums)
/*@ With l n
    Require
      0 <= n &&
      n < 2147483647 &&
      aug_last_le_array_006_pre(l) &&
      CharArray::full(nums, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == aug_last_le_array_006_spec(l) &&
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

    int last = -1;
    for (int j = 0; j < n; j++) {
        if (values[j] <= 1) {
            last = j;
        }
    }

    return last;
}
