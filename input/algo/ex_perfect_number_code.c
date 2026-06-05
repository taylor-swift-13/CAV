/*@ Extern Coq (aliquot_sum_z : Z -> Z)
               (ex_perfect_number_code_spec : Z -> Z -> Prop) */
/*@ Import Coq Require Import ex_perfect_number_code */

int ex_perfect_number_code(int n)
/*@ Require
      0 < n &&
      aliquot_sum_z(n) <= 2147483647 &&
      emp
    Ensure
      ex_perfect_number_code_spec(n, __return) &&
      emp
*/
{
    int sum = 0;

    for (int d = 1; d < n; d++) {
        if (n % d == 0) {
            sum += d;
        }
    }

    if (sum == n) {
        return 1;
    }
    if (sum > n) {
        return 2;
    }
    return 3;
}
