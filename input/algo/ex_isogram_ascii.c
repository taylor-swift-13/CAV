#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (ex_isogram_ascii_spec : list Z -> Z) */
/*@ Import Coq Require Import ex_isogram_ascii */

int ex_isogram_ascii(const char *s)
/*@ With l n
    Require
      s != 0 &&
      0 <= n && n < 2147483647 &&
      (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= 127) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_isogram_ascii_spec(l) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
*/
{
    int seen[26] = {0};

    for (int i = 0; s[i] != 0; i++) {
        char c = s[i];

        if (c >= 65 && c <= 90) {
            c = (char)(c - 65 + 97);
        }
        if (c >= 97 && c <= 122) {
            int k = c - 97;

            if (seen[k]) {
                return 0;
            }
            seen[k] = 1;
        }
    }

    return 1;
}
