/*
The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
p046_fib4(0) -> 0
p046_fib4(1) -> 0
p046_fib4(2) -> 2
p046_fib4(3) -> 0
p046_fib4(n) -> p046_fib4(n-1) + p046_fib4(n-2) + p046_fib4(n-3) + p046_fib4(n-4).
Please write a function to efficiently compute the n-th element of the p046_fib4 number sequence.  Do ! use recursion.
>>> p046_fib4(5)
4
>>> p046_fib4(6)
8
>>> p046_fib4(7)
14
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_46_pre: Z -> Prop)
               (problem_46_spec: Z -> Z -> Prop)
               (fib4: Z -> Z)
               (fib4_step_int_range: Z -> Prop) */
/*@ Import Coq Require Import p046_fib4 */

int p046_fib4(int n)
/*@ Require
        0 <= n && n < 100 &&
        problem_46_pre(n) &&
        fib4_step_int_range(n)
    Ensure
        problem_46_spec(n, __return) && emp
*/
{
    if (n == 0) {
        return 0;
    }
    if (n == 1) {
        return 0;
    }
    if (n == 2) {
        return 2;
    }
    if (n == 3) {
        return 0;
    }

    int a = 0;
    int b = 0;
    int c = 2;
    int d = 0;
    int next;
    int i;

    /*@ Inv Assert
        n == n@pre &&
        4 <= i && i <= n + 1 &&
        4 <= n &&
        n < 100 &&
        fib4_step_int_range(n) &&
        a == fib4(i - 4) &&
        b == fib4(i - 3) &&
        c == fib4(i - 2) &&
        d == fib4(i - 1) &&
        undef_data_at(&next)
    */
    for (i = 4; i <= n; i++)
    {
        next = a + b + c + d;
        a = b;
        b = c;
        c = d;
        d = next;
    }
    return d;
}
