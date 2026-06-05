#include "verification_stdlib.h"

/*@ Extern Coq (is_armstrong_z : Z -> Z) */
/*@ Import Coq Require Import armstrong_number */

int ex_armstrong_number_bool(int n)
/*@ Require
      0 <= n &&
      n <= 99999999 &&
      emp
    Ensure
      __return == is_armstrong_z(n@pre) && emp
*/
{
    int temp = n;
    int digits = 0;

    if (temp == 0) {
        digits = 1;
    }

    while (temp > 0) {
        digits++;
        temp /= 10;
    }

    temp = n;
    int sum = 0;

    while (temp > 0) {
        int d = temp % 10;
        int p = 1;
        int i = 0;

        while (i < digits) {
            p *= d;
            i++;
        }

        sum += p;
        temp /= 10;
    }

    return sum == n;
}
