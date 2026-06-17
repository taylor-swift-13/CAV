/*
Return 1 if all numbers in the vector l are below threshold t, 0 otherwise.
>>> p052_below_threshold({1, 2, 4, 10}, 100)
1
>>> p052_below_threshold({1, 20, 4, 10}, 5)
0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_52_pre: list Z -> Prop)
               (problem_52_spec: list Z -> Z -> bool -> Prop)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import p052_below_threshold */

int p052_below_threshold(int *l, int l_size, int t)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX &&
        problem_52_pre(input_l) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        ((__return != 0) && problem_52_spec(input_l, t, true) ||
         (__return == 0) && problem_52_spec(input_l, t, false)) &&
        IntArray::full(l, l_size, input_l)
*/
{
    int i;

    for (i = 0; i < l_size; i++) {
        if (l[i] >= t) {
            return 0;
        }
    }
    return 1;
}
