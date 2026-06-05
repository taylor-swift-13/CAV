#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (ex_matching_brackets_ascii_spec : list Z -> Z) */
/*@ Import Coq Require Import ex_matching_brackets_ascii */

int ex_matching_brackets_ascii(const char *s)
/*@ With l n
    Require
      s != 0 &&
      0 <= n && n <= 128 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= 127) &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_matching_brackets_ascii_spec(l) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
*/
{
    char st[128];
    int top = 0;
    int i = 0;

    while (1) {
        char c;

        if (s[i] == 0) {
            break;
        }
        c = s[i];
        if (c == 40 || c == 91 || c == 123) {
            st[top] = c;
            top++;
        } else if (c == 41 || c == 93 || c == 125) {
            char o;

            if (top == 0) {
                return 0;
            }
            top--;
            o = st[top];
            if ((c == 41 && o != 40) ||
                (c == 93 && o != 91) ||
                (c == 125 && o != 123)) {
                return 0;
            }
        }
        i++;
    }

    return top == 0;
}
