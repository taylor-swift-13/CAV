/*
You are given a vector of integers.
Write a function p090_next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

p090_next_smallest({1, 2, 3, 4, 5}) == 2
p090_next_smallest({5, 1, 4, 3, 2}) == 2
p090_next_smallest({}) == None
p090_next_smallest({1, 1}) == None
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_90_pre: list Z -> Prop)
               (problem_90_spec: list Z -> Z -> Prop)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (no_distinct_prefix: Z -> list Z -> Prop)
               (next_smallest_sorted_bridge: list Z -> list Z -> Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import p090_next_smallest */

void sort_int_array(int *array, int init_size, int size, int ascending)
/*@ With l
    Require
        array != 0 &&
        init_size == Zlength(l) &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure
        exists sorted_l sorted_full_l,
        init_size == Zlength(sorted_l) &&
        size == Zlength(sorted_full_l) &&
        sublist(0, init_size, sorted_full_l) == sorted_l &&
        sorted_int_list_by(ascending, sorted_l) &&
        Permutation(l, sorted_l) &&
        IntArray::full(array, size, sorted_full_l)
*/;

int p090_next_smallest(int *lst, int lst_size)
/*@ With input_l
    Require
        0 <= lst_size && lst_size < INT_MAX &&
        (lst_size > 1 => lst != 0) &&
        lst_size == Zlength(input_l) &&
        problem_90_pre(input_l) &&
        IntArray::full(lst, lst_size, input_l)
    Ensure
        exists final_l,
        problem_90_spec(input_l, __return) &&
        lst_size == Zlength(final_l) &&
        IntArray::full(lst, lst_size, final_l)
*/
{
    int i;

    if (lst_size <= 1) {
        return -1;
    }

    sort_int_array(lst, lst_size, lst_size, 1);

    for (i = 1; i < lst_size; i++) {
        if (lst[i] != lst[i - 1]) {
            return lst[i];
        }
    }
    return -1;
}
