/*
p040_triples_sum_to_zero takes a vector of integers as an input.
it returns true if there are three distinct elements in the vector that
sum to zero, && false otherwise.

>>> p040_triples_sum_to_zero({1, 3, 5, 0})
false
>>> p040_triples_sum_to_zero({1, 3, -2, 1})
true
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_40_pre: list Z -> Prop)
               (problem_40_spec: list Z -> bool -> Prop)
               (triple_sum_int_range: list Z -> Z -> Prop)
               (scanned_i: list Z -> Z -> Z -> Prop)
               (scanned_j: list Z -> Z -> Z -> Z -> Prop)
               (scanned_k: list Z -> Z -> Z -> Z -> Z -> Prop)
               (true: bool) (false: bool) */
/*@ Import Coq Require Import p040_triples_sum_to_zero */

int p040_triples_sum_to_zero(int *l, int l_size)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX &&
        problem_40_pre(input_l) &&
        triple_sum_int_range(input_l, l_size) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        ((__return != 0) && problem_40_spec(input_l, true) ||
         (__return == 0) && problem_40_spec(input_l, false)) &&
        IntArray::full(l, l_size, input_l)
*/
{
    int i;
    int j;
    int k;

    for (i = 0; i < l_size; i++) {

        for (j = i + 1; j < l_size; j++) {

            for (k = j + 1; k < l_size; k++) {
                if (l[i] + l[j] + l[k] == 0) {
                    return 1;
                }
            }
        }
    }
    return 0;
}
