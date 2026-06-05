/*@ Extern Coq (arithmetic_series_sum_z : Z -> Z -> Z -> Z) */
/*@ Extern Coq (arithmetic_series_pre : Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import arithmetic_series */

#include "verification_stdlib.h"

int arithmetic_series(int a, int d, int n)
/*@ Require
      arithmetic_series_pre(a, d, n) &&
      emp
    Ensure
      __return == arithmetic_series_sum_z(a@pre, d@pre, n@pre) &&
      emp
*/
{
    int i = 0;
    int cur = a;
    int sum = 0;
    while (i < n) {
        sum += cur;
        cur += d;
        i++;
    }
    return sum;
}
