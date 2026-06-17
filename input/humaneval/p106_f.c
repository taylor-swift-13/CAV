/*
Compute a sequence of size n: element at 1-indexed position i is
  factorial(i) if i is even, or triangular(i) = 1+2+...+i if i is odd.
p106_f(5) == {1, 2, 6, 24, 15}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_106_pre: Z -> Prop)
               (problem_106_spec: Z -> list Z -> Prop)
               (f_seq: Z -> list Z)
               (triangular: Z -> Z)
               (factorial: Z -> Z)
               (f_seq_int_range: Z -> Prop) */
/*@ Import Coq Require Import p106_f */

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

IntArray *p106_f(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        1 <= n0 && n0 < INT_MAX &&
        problem_106_pre(n0) &&
        f_seq_int_range(n0)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == n0 &&
        output_size == Zlength(output_l) &&
        output_l == f_seq(n0) &&
        problem_106_spec(n0, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = n;
    out->data = malloc_int_array(n);
    int *data = out->data;
    int s = 0;
    int p = 1;
    int i;

    for (i = 0; i < n; i++) {
        s += (i + 1);
        p *= (i + 1);
        if ((i + 1) % 2 == 0) {
            data[i] = p;
        }
        else {
            data[i] = s;
        }
    }
    return out;
}
