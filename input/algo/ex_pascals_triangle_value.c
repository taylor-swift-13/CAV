#include "verification_stdlib.h"

/*@ Extern Coq (ex_pascals_triangle_value_pre : Z -> Z -> Prop) */
/*@ Extern Coq (ex_pascals_triangle_value_spec : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import ex_pascals_triangle_value */

int ex_pascals_triangle_value(int row, int col)
/*@ Require
      ex_pascals_triangle_value_pre(row, col) &&
      emp
    Ensure
      ex_pascals_triangle_value_spec(row@pre, col@pre, __return) &&
      emp
*/
{
    int v[31][31];

    for (int i = 0; i <= row; i++) {
        v[i][0] = 1;
        v[i][i] = 1;
        for (int j = 1; j < i; j++) {
            v[i][j] = v[i - 1][j - 1] + v[i - 1][j];
        }
    }

    return v[row][col];
}
