/*
Implement a function that takes an non-negative integer && returns a vector of the first n
integers that are prime numbers && less than n.
for example:
p096_count_up_to(5) => {2,3}
p096_count_up_to(11) => {2,3,5,7}
p096_count_up_to(0) => {}
p096_count_up_to(20) => {2,3,5,7,11,13,17,19}
p096_count_up_to(1) => {}
p096_count_up_to(18) => {2,3,5,7,11,13,17}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_96_pre: Z -> Prop)
               (problem_96_spec: Z -> list Z -> Prop)
               (count_up_to_state: Z -> list Z -> Prop)
               (prime_test_state: Z -> list Z -> Z -> Z -> Prop) */
/*@ Import Coq Require Import p096_count_up_to */

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

IntArray *p096_count_up_to(int n)
/*@ Require
        0 <= n && n < INT_MAX &&
        problem_96_pre(n)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        output_size == Zlength(output_l) &&
        0 <= output_size && output_size <= n &&
        problem_96_spec(n, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, n)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(n);
    int *data = out->data;
    int output_size = 0;
    out->size = 0;
    int i;
    int d;

    if (n > 2) {

        for (i=2;i<n;i++)
        {
            if (output_size == 0) {

                data[output_size] = i;
                output_size = output_size + 1;
            } else {
                int j;
                int isp=1;

                j = 0;
                while (j < output_size) {
                    d = data[j];
                    if (d <= 0) {
                        break;
                    }
                    if (d > i / d) {
                        break;
                    }
                    if (i % d == 0) {
                        isp=0;
                    }
                    j = j + 1;
                }
                if (isp) {data[output_size] = i; output_size = output_size + 1;}
            }
        }
    }
    out->size = output_size;
    return out;
}
