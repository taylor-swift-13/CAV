/*
sum_to_n_60 is a function that sums numbers from 1 to n.
>>> sum_to_n_60(30)
465
>>> sum_to_n_60(100)
5050
>>> sum_to_n_60(5)
15
>>> sum_to_n_60(10)
55
>>> sum_to_n_60(1)
1
*/
#include "verification_stdlib.h"
/*@ Extern Coq (problem_60_pre_z: Z -> Prop) */
/*@ Extern Coq (problem_60_spec_z: Z -> Z -> Prop) */
/*@ Import Coq Require Import coins_60 */
int sum_to_n_60(int n)
/*@ Require
        problem_60_pre_z(n) &&
    1 <= n && n <= 46340 && emp
    Ensure
        problem_60_spec_z(n@pre, __return) && emp
*/
{
    return n*(n+1)/2;
}
