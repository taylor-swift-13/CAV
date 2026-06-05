#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (is_bin_chars : list Z -> Prop) */
/*@ Extern Coq (add_binary_strings_spec : list Z -> list Z -> list Z) */
/*@ Import Coq Require Import add_binary_strings */

char *malloc_char_array(int n)
/*@ Require n > 0 && emp
    Ensure exists l, CharArray::full(__return, n, l)
*/
;

char *add_binary_strings(const char *a, const char *b)
/*@ With la lb na nb
    Require
      a != 0 &&
      b != 0 &&
      1 <= na &&
      1 <= nb &&
      na + nb + 1 <= 2147483647 &&
      Zlength(la) == na &&
      Zlength(lb) == nb &&
      is_bin_chars(la) &&
      is_bin_chars(lb) &&
      CharArray::full((char *)a, na + 1, app(la, cons(0, nil))) *
      CharArray::full((char *)b, nb + 1, app(lb, cons(0, nil)))
    Ensure
      exists t,
        Zlength(t) == na + nb - Zlength(add_binary_strings_spec(la, lb)) &&
        CharArray::full((char *)a, na + 1, app(la, cons(0, nil))) *
        CharArray::full((char *)b, nb + 1, app(lb, cons(0, nil))) *
        CharArray::full(__return, na + nb + 1,
          app(app(add_binary_strings_spec(la, lb), cons(0, nil)), t))
*/
{
    int na = 0;
    int nb = 0;

    while (1) {
        if (a[na] == 0) {
            break;
        }
        na++;
    }
    while (1) {
        if (b[nb] == 0) {
            break;
        }
        nb++;
    }

    int total = na + nb;

    char *out = malloc_char_array(total + 1);
    int i = na - 1;
    int j = nb - 1;
    int pos = total - 1;
    int carry = 0;

    out[total] = 0;

    while (i >= 0 || j >= 0 || carry) {
        int sum = carry;
        if (i >= 0) {
            sum += a[i] - 48;
            i--;
        }
        if (j >= 0) {
            sum += b[j] - 48;
            j--;
        }
        out[pos] = (char)(48 + (sum % 2));
        carry = sum / 2;
        pos--;
    }

    while (pos >= 0) {
        out[pos] = 48;
        pos--;
    }

    int start = 0;
    while (start < total - 1 && out[start] == 48) {
        start++;
    }

    int k = 0;
    while (start + k <= total) {
        out[k] = out[start + k];
        k++;
    }

    return out;
}
