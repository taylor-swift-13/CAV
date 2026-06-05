#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (ex_matrix_row_sum_pre : list Z -> Z -> Prop) */
/*@ Extern Coq (ex_matrix_row_sum_spec : list Z -> Z -> Z) */
/*@ Import Coq Require Import ex_matrix_row_sum */

int ex_matrix_row_sum(const char *rows, int row)
/*@ With l n
    Require
      rows != 0 &&
      0 <= n &&
      n <= 2147483646 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      ex_matrix_row_sum_pre(l, row) &&
      CharArray::full((char *)rows, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == ex_matrix_row_sum_spec(l, row) &&
      CharArray::full((char *)rows, n + 1, app(l, cons(0, nil)))
*/
{
    int current = 1;
    int i = 0;
    int sum = 0;

    while (1) {
        if (rows[i] == 0) {
            break;
        }

        int sign = 1;
        int v = 0;

        if (rows[i] == 45) {
            sign = -1;
            i++;
        }

        while (rows[i] >= 48 && rows[i] <= 57) {
            v = v * 10 + (rows[i] - 48);
            i++;
        }

        if (current == row) {
            sum += sign * v;
        }

        if (rows[i] == 59) {
            current++;
            i++;
        } else if (rows[i] == 44) {
            i++;
        }
    }

    return sum;
}
