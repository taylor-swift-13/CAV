/*
The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial_139(4)
288

The function will receive an integer as input && should return the special
factorial of this integer.
*/
#include "verification_stdlib.h"
/*@ Extern Coq (factorial: Z -> Z)
               (bfact_coq: Z -> Z) */
/*@ Extern Coq (problem_139_pre: Z -> Prop) */
/*@ Extern Coq (problem_139_spec: Z -> Z -> Prop) */
/*@ Import Coq Require Import special_factorial_139 */
long long special_factorial_139(int n)
/*@ Require
        problem_139_pre(n) &&
        1 <= n && n <= 8 && emp
    Ensure
        problem_139_spec(n@pre, __return) && emp
*/
{
    long long fact=1,bfact=1;
    int i;
    
    for (i=1;i<=n;i++)
    {
        fact=fact*i;
        bfact=bfact*fact;
    }
    return bfact;
}
