/*
Given a positive integer n, return the product of the odd p131_digits.
Return 0 if all p131_digits are even.
For example:
p131_digits(1)  == 1
p131_digits(4)  == 0
p131_digits(235) == 15
*/
#include "verification_stdlib.h"
/*@ Extern Coq (problem_131_pre: Z -> Prop) */
/*@ Extern Coq (problem_131_spec: Z -> Z -> Prop) */
/*@ Extern Coq (tail_odd_prod: Z -> Z) */
/*@ Extern Coq (digits_state: Z -> Z -> Z -> Z) */
/*@ Import Coq Require Import p131_digits */
int p131_digits(int n)
/*@ Require
        problem_131_pre(n) &&
        1 <= n && n <= INT_MAX &&
    tail_odd_prod(n) <= INT_MAX && emp
    Ensure
    problem_131_spec(n@pre, __return) && emp
*/
{
    int prod=1,has=0;
    if (n == 0) return 0;
    /*@ Inv Assert
        exists n0,
        n0 == n@pre &&
        1 <= n0 &&
        0 <= n && n <= n0 &&
        (has == 0 || has == 1) &&
        1 <= prod && prod <= INT_MAX &&
        tail_odd_prod(n0) == digits_state(n, prod, has) &&
        digits_state(n, prod, has) <= INT_MAX &&
        emp
    */
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
