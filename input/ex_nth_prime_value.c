#include "../verification_stdlib.h"

/*@ Extern Coq (ex_nth_prime_value_pre : Z -> Prop) */
/*@ Extern Coq (ex_nth_prime_value_spec : Z -> Z -> Prop) */
/*@ Import Coq Require Import ex_nth_prime_value */

int ex_nth_prime_value(int n)
/*@ Require
      ex_nth_prime_value_pre(n) &&
      emp
    Ensure
      ex_nth_prime_value_spec(n@pre, __return) &&
      emp
*/
{
    int count = 0;
    int x = 2;

    while (1) {
        int prime = 1;
        int d = 2;

        while (d <= x / d) {
            if (x % d == 0) {
                prime = 0;
            }
            d++;
        }

        if (prime) {
            count++;
            if (count == n) {
                return x;
            }
        }

        x++;
    }
}
