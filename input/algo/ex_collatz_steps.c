#include "verification_stdlib.h"

/*@ Extern Coq (ex_collatz_safe_fuel : Z -> Z -> Prop) */
/*@ Extern Coq (ex_collatz_steps_fuel : Z -> Z -> Z) */
/*@ Import Coq Require Import ex_collatz_steps */

int ex_collatz_steps(int n)
/*@ With fuel
    Require
      1 <= n &&
      0 <= fuel &&
      fuel <= 2147483647 &&
      ex_collatz_safe_fuel(n, fuel) &&
      emp
    Ensure
      __return == ex_collatz_steps_fuel(n@pre, fuel) &&
      emp
*/
{
    long long x = n;
    int steps = 0;

    while (x != 1) {
        if (x % 2 == 0) {
            x /= 2;
        } else {
            x = 3 * x + 1;
        }
        steps++;
    }

    return steps;
}
