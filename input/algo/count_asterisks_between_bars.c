#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (count_asterisks_between_bars_spec : list Z -> Z) */
/*@ Import Coq Require Import count_asterisks_between_bars */

int count_asterisks_between_bars(char *s)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == count_asterisks_between_bars_spec(l) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
{
    int inside = 0;
    int count = 0;
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == 124) {
            inside = !inside;
        } else if (s[i] == 42 && inside) {
            count++;
        }
        i++;
    }

    return count;
}
