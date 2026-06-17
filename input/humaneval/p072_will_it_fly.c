/*
Write a function that returns 1 if the object q will fly, && 0 otherwise.
The object q will fly if it's balanced (it is a palindromic vector) && the sum of its elements
is less than || equal the maximum possible weight w.
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_72_pre: list Z -> Z -> Prop)
               (problem_72_spec: list Z -> Z -> Z -> Prop)
               (will_it_fly_int_range: list Z -> Prop) */
/*@ Import Coq Require Import p072_will_it_fly */

int p072_will_it_fly(int *q, int q_size, int w)
/*@ With lv
    Require
        0 <= q_size && q_size < INT_MAX &&
        q_size == Zlength(lv) &&
        problem_72_pre(lv, w) &&
        will_it_fly_int_range(lv) &&
        IntArray::full(q, q_size, lv)
    Ensure
        problem_72_spec(lv, w, __return) &&
        IntArray::full(q, q_size, lv)
*/
{
    int s = 0;
    int i;

    for (i = 0; i < q_size; i++) {
        if (q[i] != q[q_size - 1 - i]) {
            return 0;
        }
        s += q[i];
    }
    if (s > w) {
        return 0;
    }
    return 1;
}
