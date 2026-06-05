#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (ex_binary_search_index_csv_pre : list Z -> Prop) */
/*@ Extern Coq (ex_binary_search_index_csv_spec : list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import ex_binary_search_index_csv */

int ex_binary_search_index_csv(const char *nums, int target)
/*@ With l n
    Require
      nums != 0 &&
      0 <= n &&
      n <= 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      ex_binary_search_index_csv_pre(l) &&
      CharArray::full((char *)nums, n + 1, app(l, cons(0, nil)))
    Ensure
      ex_binary_search_index_csv_spec(l, target, __return) &&
      CharArray::full((char *)nums, n + 1, app(l, cons(0, nil)))
*/
{
    if (nums[0] == 0) return -1;

    int a[128];
    int count = 0;
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

        a[count] = sign * v;
        count++;

        if (nums[i] == 44) i++;
    }

    int left = 0;
    int right = count - 1;

    while (left <= right) {
        int mid = left + (right - left) / 2;
        if (a[mid] == target) return mid;
        if (a[mid] < target) {
            left = mid + 1;
        } else {
            right = mid - 1;
        }
    }

    return -1;
}
