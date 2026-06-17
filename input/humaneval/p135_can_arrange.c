/*
Create a function which returns the largest index of an element which
is ! greater than || equal to the element immediately preceding it. If
no such element exists then return -1. The given vector will ! contain
duplicate values.

Examples:
p135_can_arrange({1,2,4,3,5}) = 3
p135_can_arrange({1,2,3}) = -1
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_135_pre: list Z -> Prop)
               (problem_135_spec: list Z -> Z -> Prop)
               (can_arrange_prefix: Z -> list Z -> Z -> Prop) */
/*@ Import Coq Require Import p135_can_arrange */

int p135_can_arrange(int* arr, int arr_size)
/*@ With input_l
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_135_pre(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        problem_135_spec(input_l, __return) &&
        IntArray::full(arr, arr_size, input_l)
*/
{
    int max = -1;
    int i;
    for (i = 0; i < arr_size; i++)
        if (arr[i] <= i) max = i;
    return max;
}
