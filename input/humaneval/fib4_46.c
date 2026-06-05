/*
The Fib4 number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fib4_46(0) -> 0
fib4_46(1) -> 0
fib4_46(2) -> 2
fib4_46(3) -> 0
fib4_46(n) -> fib4_46(n-1) + fib4_46(n-2) + fib4_46(n-3) + fib4_46(n-4).
Please write a function to efficiently compute the n-th element of the fib4_46 number sequence.  Do ! use recursion.
>>> fib4_46(5)
4
>>> fib4_46(6)
8
>>> fib4_46(7)
14
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_46_pre_z: Z -> Prop)
               (problem_46_spec_z: Z -> Z -> Prop)
               (fib4_z: Z -> Z)
               (fib4_step_int_range: Z -> Prop) */
/*@ Import Coq Require Import coins_46 */

int fib4_46(int n)
/*@ Require
        0 <= n && n < 100 &&
        problem_46_pre_z(n) &&
        fib4_step_int_range(n)
    Ensure
        problem_46_spec_z(n, __return) && emp
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
