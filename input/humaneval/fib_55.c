/*
Return n-th Fibonacci number (1-indexed: fib_55(1)=1, fib_55(2)=1, fib_55(3)=2, ...).
Rewritten to avoid local arrays: uses two rolling variables.
>>> fib_55(10) = 55
>>> fib_55(1)  = 1
>>> fib_55(8)  = 21
*/
#include "verification_stdlib.h"

/*@ Extern Coq (problem_55_pre: Z -> Prop)
               (problem_55_spec: Z -> Z -> Prop)
               (fib_seq: Z -> Z)
               (fib_step_int_range: Z -> Prop) */
/*@ Import Coq Require Import fib_55 */

int fib_55(int n)
/*@ Require
        1 <= n && n < 100 &&
        problem_55_pre(n) &&
        fib_step_int_range(n) && emp
    Ensure problem_55_spec(n, __return) && emp
*/
{
    int a;
    int b;
    int c;
    int i;
    a = 0;
    b = 1;
    
    for (i = 2; i <= n; i++) {
        c = a + b;
        a = b;
        b = c;
    }
    return b;
}
