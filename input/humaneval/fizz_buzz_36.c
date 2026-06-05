/*
Return the number of times the digit 7 appears in integers less than n which are divisible by 11 or 13.
>>> fizz_buzz_36(50)
0
>>> fizz_buzz_36(78)
2
>>> fizz_buzz_36(79)
3
*/
#include "verification_stdlib.h"

/*@ Extern Coq (fizzbuzz_upto: Z -> Z)
               (count_digit7: Z -> Z) */
/*@ Extern Coq (problem_36_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_36 */

int fizz_buzz_36(int n)
/*@ Require
        0 <= n && n <= 46340 && emp
    Ensure
        problem_36_spec_z(n@pre, __return) && emp
*/
{
    int count = 0;
    int i;
    int q;
    
    for (i = 0; i < n; i++)
    if (i % 11 == 0)
    {
        q = i;
        
        while (q > 0)
        {
            if (q % 10 == 7) count += 1;
            q = q / 10;
        }
    }
    else if (i % 13 == 0)
    {
        q = i;
        
        while (q > 0)
        {
            if (q % 10 == 7) count += 1;
            q = q / 10;
        }
    }
    return count;
}
