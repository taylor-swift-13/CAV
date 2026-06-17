/*
Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
p130_tri(1) = 3
p130_tri(n) = 1 + n / 2, if n is even.
p130_tri(n) =  p130_tri(n - 1) + p130_tri(n - 2) + p130_tri(n + 1), if n is odd.
For example:
p130_tri(2) = 1 + (2 / 2) = 2
p130_tri(4) = 3
p130_tri(3) = p130_tri(2) + p130_tri(1) + p130_tri(4)
       = 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a vector of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
p130_tri(3) = {1, 3, 2, 8}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_130_pre: Z -> Prop)
               (problem_130_spec: Z -> list Z -> Prop)
               (tri_sequence: Z -> list Z)
               (tri_seq_int_range: Z -> Prop) */
/*@ Import Coq Require Import p130_tri */

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

IntArray *p130_tri(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        0 <= n0 && n0 + 1 < INT_MAX &&
        problem_130_pre(n0) &&
        tri_seq_int_range(n0)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == n0 + 1 &&
        output_size == Zlength(output_l) &&
        output_l == tri_sequence(n0) &&
        problem_130_spec(n0, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = n + 1;
    out->data = malloc_int_array(n + 1);
    int *data = out->data;
    data[0] = 1;
    if (n == 0) return out;
    data[1] = 3;
    int i;
    for (i = 2; i <= n; i++)
    {
        if (i % 2 == 0) data[i] = 1 + i / 2;
        else data[i] = data[i - 1] + data[i - 2] + 1 + (i + 1) / 2;
    }
    return out;
}
