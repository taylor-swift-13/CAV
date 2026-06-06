/*
You are given a vector arr of integers && you need to return
sum of magnitudes of integers multiplied by product of all signs
of each number in the vector, represented by 1, -1 || 0.
Note: return -32768 for empty arr.

Example:
>>> p128_prod_signs({1, 2, 2, -4}) == -9
>>> p128_prod_signs({0, 1}) == 0
>>> p128_prod_signs({}) == -32768
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (Zabs: Z -> Z)
               (problem_128_pre: list Z -> Prop)
               (problem_128_spec: list Z -> Z -> Prop)
               (prod_signs_prefix: Z -> list Z -> Z -> Z -> Prop)
               (prod_signs_int_range: list Z -> Prop) */
/*@ Import Coq Require Import p128_prod_signs */

int abs(int x)
/*@ Require
        INT_MIN < x && x <= INT_MAX && emp
    Ensure
        __return == Zabs(x) && emp
*/
{
    if (x < 0) return -x;
    else return x;
}

int p128_prod_signs(int* arr, int arr_size)
/*@ With input_l
    Require
        0 <= arr_size && arr_size < INT_MAX &&
        arr_size == Zlength(input_l) &&
        problem_128_pre(input_l) &&
        prod_signs_int_range(input_l) &&
        IntArray::full(arr, arr_size, input_l)
    Ensure
        problem_128_spec(input_l, __return) &&
        IntArray::full(arr, arr_size, input_l)
*/
{
    if (arr_size == 0) return -32768;
    int i, sum = 0, prods = 1;

    for (i = 0; i < arr_size; i++)
    {
        int current = arr[i];
        int mag = abs(current);

        sum += mag;
        if (current == 0) prods = 0;
        if (current < 0) prods = -prods;
   }
   return sum * prods;
}
