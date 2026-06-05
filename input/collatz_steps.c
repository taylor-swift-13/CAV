#include "../verification_stdlib.h"

/*@ Extern Coq (collatz_safe_fuel : Z -> Z -> Prop) */
/*@ Extern Coq (collatz_steps_fuel : Z -> Z -> Z) */
/*@ Import Coq Require Import collatz_steps */

int collatz_steps(int n)
/*@ With fuel
    Require
      1 <= n &&
      0 <= fuel &&
      collatz_safe_fuel(n, fuel) &&
      emp
    Ensure
      __return == collatz_steps_fuel(n@pre, fuel) &&
      emp
*/
{
    int steps = 0;

    while (n != 1) {
        if (n % 2 == 0) {
            n /= 2;
        } else {
            n = 3 * n + 1;
        }
        steps++;
    }

    return steps;
}
