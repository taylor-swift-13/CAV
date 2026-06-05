/*
Given a positive integer n, return the product of the odd digits_131.
Return 0 if all digits_131 are even.
For example:
digits_131(1)  == 1
digits_131(4)  == 0
digits_131(235) == 15
*/
#include "verification_stdlib.h"
/*@ Extern Coq (problem_131_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_131_spec_z: Z -> Z -> Prop) */
/*@ Extern Coq (tail_odd_prod_z: Z -> Z) */
/*@ Extern Coq (digits_state_z: Z -> Z -> Z -> Z) */
/*@ Import Coq Require Import coins_131 */
int digits_131(int n)
/*@ Require
        problem_131_pre_z(n) &&
        1 <= n && n <= INT_MAX &&
    tail_odd_prod_z(n) <= INT_MAX && emp
    Ensure
    problem_131_spec_z(n@pre, __return) && emp
*/
{
    int prod=1,has=0;
    if (n == 0) return 0;
    
    while (n > 0) {
        int d = n % 10;
        if (d % 2 == 1) {
            has = 1;
            prod *= d;
        }
        n /= 10;
    }
    if (has==0) return 0;
    return prod;
}
