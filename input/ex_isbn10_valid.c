#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (ex_isbn10_valid_spec : list Z -> Z) */
/*@ Import Coq Require Import ex_isbn10_valid */

int ex_isbn10_valid(const char *s)
/*@ With l n
    Require
      s != 0 &&
      0 <= n && n < 2147483647 &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_isbn10_valid_spec(l) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
*/
{
    int pos = 0;
    int sum = 0;
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }

        if (s[i] == 45) {
            i++;
            continue;
        }

        if (s[i] == 88) {
            if (pos != 9) {
                return 0;
            }
            sum += 10 * (10 - pos);
            pos++;
            i++;
            continue;
        }

        if (48 <= s[i] && s[i] <= 57) {
            if (pos >= 10) {
                return 0;
            }
            sum += (s[i] - 48) * (10 - pos);
            pos++;
            i++;
            continue;
        }

        return 0;
    }

    return pos == 10 && sum % 11 == 0;
}
