/*
Given a positive integer n, make a pile of n levels of stones.
Level i (0-indexed) has n + 2*i stones (always increments by 2).

>>> p100_make_a_pile(3) => {3, 5, 7}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_100_pre: Z -> Prop)
               (problem_100_spec: Z -> list Z -> Prop)
               (pile_int_range: Z -> Prop)
               (make_pile: Z -> list Z) */
/*@ Import Coq Require Import p100_make_a_pile */

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;

int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;

IntArray *p100_make_a_pile(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        1 <= n0 && n0 < INT_MAX &&
        problem_100_pre(n0) &&
        pile_int_range(n0)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == n0 &&
        output_size == Zlength(output_l) &&
        output_l == make_pile(n0) &&
        problem_100_spec(n0, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = n;
    out->data = malloc_int_array(n);
    int *data = out->data;
    int i;

    for (i = 0; i < n; i++){
        data[i] = n + 2 * i;
    }
    return out;
}
