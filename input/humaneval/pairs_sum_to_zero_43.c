/*
pairs_sum_to_zero_43 takes a vector of integers as an input.
it returns true if there are two distinct elements in the vector that
sum to zero, && false otherwise.
>>> pairs_sum_to_zero_43({1, 3, 5, 0})
false
>>> pairs_sum_to_zero_43({2, 4, -5, 3, 5, 7})
true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_43_pre: list Z -> Prop)
               (problem_43_spec: list Z -> bool -> Prop)
               (pair_sum_int_range: list Z -> Z -> Prop)
               (scanned_i: list Z -> Z -> Z -> Prop)
               (scanned_j: list Z -> Z -> Z -> Z -> Prop)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import pairs_sum_to_zero_43 */

int pairs_sum_to_zero_43(int *l, int l_size)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX &&
        problem_43_pre(input_l) &&
        pair_sum_int_range(input_l, l_size) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        ((__return != 0) && problem_43_spec(input_l, true) ||
         (__return == 0) && problem_43_spec(input_l, false)) &&
        IntArray::full(l, l_size, input_l)
*/
{
    int i;
    int j;

    for (i = 0; i < l_size; i++) {

        for (j = i + 1; j < l_size; j++)
            if (l[i] + l[j] == 0) return 1;
    }
    return 0;
}
