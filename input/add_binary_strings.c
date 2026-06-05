#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (bin_val_aux : list Z -> Z -> Z) */
/*@ Extern Coq (bin_val : list Z -> Z) */
/*@ Extern Coq (is_bin_list : list Z -> Prop) */
/*@ Extern Coq (is_canonical : list Z -> Prop) */
/*@ Import Coq Require Import add_binary_strings */

void add_binary_strings(char *a, int na, char *b, int nb, char *out)
/*@ With la lb
    Require
      a != 0 && b != 0 && out != 0 &&
      1 <= na &&
      1 <= nb &&
      na + nb <= 2147483645 &&
      Zlength(la) == na &&
      Zlength(lb) == nb &&
      is_bin_list(la) &&
      is_bin_list(lb) &&
      CharArray::full(a, na + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb + 1, app(lb, cons(0, nil))) *
      CharArray::undef_full(out, na + nb + 2)
    Ensure exists r,
      1 <= Zlength(r) &&
      Zlength(r) <= na@pre + nb@pre + 1 &&
      is_bin_list(r) &&
      is_canonical(r) &&
      bin_val(r) == bin_val(la) + bin_val(lb) &&
      CharArray::full(a, na@pre + 1, app(la, cons(0, nil))) *
      CharArray::full(b, nb@pre + 1, app(lb, cons(0, nil))) *
      CharArray::full(out, na@pre + nb@pre + 2,
        app(r, cons(0, repeat_Z(0, na@pre + nb@pre + 1 - Zlength(r)))))
*/
{
    int i;
    int j;
    int carry = 0;
    int pos = 0;

    i = na - 1;
    j = nb - 1;

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
        out[pos] = 48 + sum % 2;
        carry = sum / 2;
        pos++;
    }

    while (pos > 1 && out[pos - 1] == 48) {
        pos--;
    }

    int lo = 0;
    int hi = pos - 1;
    while (lo < hi) {
        char tmp = out[lo];
        out[lo] = out[hi];
        out[hi] = tmp;
        lo++;
        hi--;
    }

    out[pos] = 0;

    int fill = pos + 1;
    while (fill < na + nb + 2) {
        out[fill] = 0;
        fill++;
    }
}
