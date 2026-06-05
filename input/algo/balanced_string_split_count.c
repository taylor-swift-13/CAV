#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (balanced_string_split_count_pre : list Z -> Prop) */
/*@ Extern Coq (balanced_string_split_count_spec : list Z -> Z) */
/*@ Import Coq Require Import balanced_string_split_count */

int balanced_string_split_count(char *s)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      balanced_string_split_count_pre(l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == balanced_string_split_count_spec(l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int balance = 0;
    int count = 0;
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == 76) {
            balance++;
        } else {
            balance--;
        }
        if (balance == 0) {
            count++;
        }
        i++;
    }

    return count;
}
