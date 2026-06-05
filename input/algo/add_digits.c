#include "verification_stdlib.h"

/*@ Extern Coq (digital_root_z : Z -> Z) */
/*@ Import Coq Require Import add_digits */

int add_digits(int num)
/*@ Require
      0 <= num && emp
    Ensure
      __return == digital_root_z(num@pre) && emp
*/
{
    while (num >= 10) {
        int sum = 0;
        while (num > 0) {
            sum += num % 10;
            num /= 10;
        }
        num = sum;
    }
    return num;
}
