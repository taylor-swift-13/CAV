/*
Given a vector arr of integers, find the minimum number of elements that
need to be changed to make the vector palindromic. A palindromic vector is a vector that
is read the same backwards && forwards. In one change, you can change one element to any other element.

For example:
p073_smallest_change({1,2,3,5,4,7,9,6}) == 4
p073_smallest_change({1, 2, 3, 4, 3, 2, 2}) == 1
p073_smallest_change({1, 2, 3, 2, 1}) == 0
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_73_pre: list Z -> Prop)
               (problem_73_spec: list Z -> Z -> Prop)
               (count_half_mismatches_upto: Z -> list Z -> Z)
               (smallest_change_int_range: list Z -> Prop) */
/*@ Import Coq Require Import p073_smallest_change */

int p073_smallest_change(int *arr, int arr_size)
/*@ With lv
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(lv) &&
        problem_73_pre(lv) &&
        smallest_change_int_range(lv) &&
        IntArray::full(arr, arr_size, lv)
    Ensure
        problem_73_spec(lv, __return) &&
        IntArray::full(arr, arr_size, lv)
*/
{
    int out = 0;
    int i;

    for (i = 0; i < arr_size - 1 - i; i++) {
        if (arr[i] != arr[arr_size - 1 - i])
            out += 1;
    }
    return out;
}
