/*
Return a pointer to a newly allocated IntArray containing the prime factors of
given integer in the order from smallest to largest.
Each of the factors should be vectored number of times corresponding to how many times it appeares in factorization.
Input number should be equal to the product of all factors
>>> p025_factorize(8)
{2, 2, 2}
>>> p025_factorize(25)
{5, 5}
>>> p025_factorize(70)
{2, 5, 7}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_25_pre: Z -> Prop)
               (problem_25_spec: Z -> list Z -> Prop)
               (factorize_loop_state: Z -> Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import p025_factorize */

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

IntArray *p025_factorize(int n)
/*@ With (n0: Z)
    Require
        n == n0 &&
        2 <= n0 && n0 < INT_MAX &&
        problem_25_pre(n0)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= n0 &&
        problem_25_spec(n0, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, n0)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(n);
    int *data = out->data;

    for (int i=2;i<=n/i;i++) {
        if (n%i==0)
        {
            n=n/i;
            data[out->size] = i;
            out->size = out->size + 1;
            i-=1;
        }
    }
    data[out->size] = n;
    out->size = out->size + 1;
    return out;
}
