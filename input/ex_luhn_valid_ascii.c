#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (ex_luhn_valid_ascii_pre : list Z -> Prop) */
/*@ Extern Coq (ex_luhn_valid_ascii_spec : list Z -> Z) */
/*@ Import Coq Require Import ex_luhn_valid_ascii */

int ex_luhn_valid_ascii(const char *s)
/*@ With l n
    Require
      s != 0 &&
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      ex_luhn_valid_ascii_pre(l) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_luhn_valid_ascii_spec(l) &&
      CharArray::full((char *)s, n + 1, app(l, cons(0, nil)))
*/
{
    int digits[128];
    int digits_len = 0;
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == 32) {
            i++;
            continue;
        }
        if (s[i] < 48 || s[i] > 57) {
            return 0;
        }
        digits[digits_len] = s[i] - 48;
        digits_len++;
        i++;
    }

    if (digits_len < 2) {
        return 0;
    }

    int sum = 0;
    int dbl = 0;
    i = digits_len - 1;
    while (i >= 0) {
        int v = digits[i];
        if (dbl) {
            v = v * 2;
            if (v > 9) {
                v = v - 9;
            }
        }
        sum += v;
        dbl = !dbl;
        i--;
    }

    return sum % 10 == 0;
}
