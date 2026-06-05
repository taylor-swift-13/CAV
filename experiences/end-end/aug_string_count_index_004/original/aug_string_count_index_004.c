#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (aug_string_count_index_004_spec : list Z -> Z) */
/*@ Import Coq Require Import aug_string_count_index_004 */

int aug_string_count_index_004(char *s)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == aug_string_count_index_004_spec(l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int count = 0;
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == 101) {
            count++;
        }
        i++;
    }

    return count;
}
