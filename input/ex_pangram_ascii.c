#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (ex_pangram_ascii_spec : list Z -> Z) */
/*@ Import Coq Require Import ex_pangram_ascii */

int ex_pangram_ascii(const char *s)
/*@ With l n
    Require
      s != 0 &&
      0 <= n && n < 2147483647 &&
      (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= 127) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_pangram_ascii_spec(l) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
*/
{
    int target = 0;

    while (target < 26) {
        int i = 0;
        int found = 0;

        while (1) {
            char c;

            if (s[i] == 0) {
                break;
            }
            c = s[i];
            if (c >= 65 && c <= 90) {
                c = (char)(c - 65 + 97);
            }
            if (c == target + 97) {
                found = 1;
                break;
            }
            i++;
        }
        if (!found) {
            return 0;
        }
        target++;
    }

    return 1;
}
