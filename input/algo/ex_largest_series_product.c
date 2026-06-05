#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (ex_largest_series_product_pre : list Z -> Z -> Prop) */
/*@ Extern Coq (ex_largest_series_product_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import ex_largest_series_product */

int ex_largest_series_product(const char *digits, int span)
/*@ With l n
    Require
      digits != 0 &&
      0 <= n && n <= 2147483647 &&
      Zlength(l) == n &&
      ex_largest_series_product_pre(l, span) &&
      CharArray::full(digits, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_largest_series_product_spec(l, span) &&
      CharArray::full(digits, n + 1, app(l, cons(0, nil)))
*/
{
    int n = 0;

    while (1) {
        if (digits[n] == 0) {
            break;
        }
        n++;
    }

    if (span == 0) {
        return 1;
    }

    int best = 0;

    for (int i = 0; i + span <= n; i++) {
        int p = 1;

        for (int j = 0; j < span; j++) {
            p *= digits[i + j] - 48;
        }

        if (p > best) {
            best = p;
        }
    }

    return best;
}
