/*
The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
p063_fibfib(0) == 0
p063_fibfib(1) == 0
p063_fibfib(2) == 1
p063_fibfib(n) == p063_fibfib(n-1) + p063_fibfib(n-2) + p063_fibfib(n-3).
Please write a function to efficiently compute the n-th element of the p063_fibfib number sequence.
>>> p063_fibfib(1)
0
>>> p063_fibfib(5)
4
>>> p063_fibfib(8)
24
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_63_pre: Z -> Prop)
               (problem_63_spec: Z -> Z -> Prop)
               (fibfib: Z -> Z)
               (fibfib_step_int_range: Z -> Prop) */
/*@ Import Coq Require Import p063_fibfib */

int p063_fibfib(int n)
/*@ Require
        0 <= n && n < 100 &&
        problem_63_pre(n) &&
        fibfib_step_int_range(n)
    Ensure
        problem_63_spec(n, __return) && emp
*/
{
    if (n == 0) {
        return 0;
    }
    if (n == 1) {
        return 0;
    }
    if (n == 2) {
        return 1;
    }

    int a = 0;
    int b = 0;
    int c = 1;
    int next;
    int i;

    for (i = 3; i <= n; i++) {
        next = a + b + c;
        a = b;
        b = c;
        c = next;
    }
    return c;
}
