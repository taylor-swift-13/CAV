/*
This function takes a vector l and returns a vector l' such that l' is
identical to l at indices that are not divisible by three, while the values at
indices divisible by three are the corresponding values of l, but sorted.

>>> sort_third_33({1, 2, 3})
{1, 2, 3}
>>> sort_third_33({5, 6, 3, 4, 8, 9, 2})
{2, 6, 3, 4, 8, 9, 5}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_33_pre_z: list Z -> Prop)
               (problem_33_spec_z: list Z -> list Z -> Prop)
               (third_count: Z -> Z)
               (third_values_prefix: Z -> list Z -> list Z)
               (sort_third_output_prefix: Z -> list Z -> list Z -> list Z)
               (sort_third_output: list Z -> list Z -> list Z)
               (sorted_int_list_by: Z -> list Z -> Prop)
               (Permutation: list Z -> list Z -> Prop) */
/*@ Import Coq Require Import coins_33 */

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

void free_int_array(int *array, int size)
/*@ Require
        exists l,
        array != 0 &&
        0 <= size && size < INT_MAX &&
        size == Zlength(l) &&
        IntArray::full(array, size, l)
    Ensure emp
*/;

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

IntArray *sort_third_33(int *l, int l_size)
/*@ With input_l
    Require
        0 <= l_size && l_size < INT_MAX - 2 &&
        l_size == Zlength(input_l) &&
        problem_33_pre_z(input_l) &&
        IntArray::full(l, l_size, input_l)
    Ensure
        exists data output_l output_size,
        __return != 0 &&
        data != 0 &&
        output_size == l_size &&
        output_size == Zlength(output_l) &&
        problem_33_spec_z(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(data, output_size, output_l) *
        IntArray::full(l, l_size, input_l)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = l_size;
    out->data = malloc_int_array(l_size);
    int *data = out->data;
    int third_size = (l_size + 2) / 3;
    int *third = malloc_int_array(l_size);
    int i;
    int j;

    for (i = 0; i * 3 < l_size; i++)
        third[i] = l[i * 3];

    sort_int_array(third, third_size, l_size, 1);

    j = 0;
    
    for (i = 0; i < l_size; i++)
    {
        if (i % 3 == 0) { data[i] = third[j]; j = j + 1; }
        else data[i] = l[i];
    }

    free_int_array(third, l_size);
    return out;
}
