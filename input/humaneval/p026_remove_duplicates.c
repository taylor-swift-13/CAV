/*
From a vector of integers, remove all elements that occur more than once.
Keep order of elements left the same as in the input.
>>> p026_remove_duplicates({1, 2, 3, 2, 4})
{1, 3, 4}
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_26_pre: list Z -> Prop)
               (problem_26_spec: list Z -> list Z -> Prop)
               (list_contains: Z -> list Z -> Prop)
               (list_not_contains: Z -> list Z -> Prop)
               (remove_duplicates_first_loop: list Z -> Z -> list Z -> list Z -> Prop)
               (remove_duplicates_second_loop: list Z -> list Z -> Z -> list Z -> Prop) */
/*@ Import Coq Require Import p026_remove_duplicates */

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

void free_int_array(int *array, int init_size, int size)
/*@ Require
        exists l,
        array != 0 &&
        0 <= init_size && init_size <= size &&
        0 <= size && size < INT_MAX &&
        IntArray::seg(array, 0, init_size, l) *
        IntArray::undef_seg(array, init_size, size)
    Ensure emp
*/;

int contains(int *a, int n, int x)
/*@ With l
    Require
        0 <= n && n < INT_MAX &&
        n == Zlength(l) &&
        IntArray::seg(a, 0, n, l)
    Ensure
        ((__return != 0) && list_contains(x, l) ||
         (__return == 0) && list_not_contains(x, l)) &&
        n == Zlength(l) &&
        IntArray::seg(a, 0, n, l)
*/
{
    int i;
    for (i = 0; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }
    return 0;
}

IntArray *p026_remove_duplicates(int *numbers, int numbers_size)
/*@ With input_l
    Require
        0 <= numbers_size && numbers_size < INT_MAX &&
        numbers_size == Zlength(input_l) &&
        problem_26_pre(input_l) &&
        IntArray::full(numbers, numbers_size, input_l)
    Ensure
        exists data output_l output_size,
            __return != 0 &&
            0 <= output_size && output_size <= numbers_size &&
            numbers_size == Zlength(input_l) &&
            output_size == Zlength(output_l) &&
            problem_26_spec(input_l, output_l) &&
        data_at(&(__return -> data), data) *
        data_at(&(__return -> size), output_size) *
        IntArray::full(numbers, numbers_size, input_l) *
        IntArray::seg(data, 0, output_size, output_l) *
        IntArray::undef_seg(data, output_size, numbers_size)
*/
{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(numbers_size);
    int *data = out->data;
    int *has1 = malloc_int_array(numbers_size);
    int has1_size = 0;
    int *has2 = malloc_int_array(numbers_size);
    int has2_size = 0;
    int i;

    for (i = 0; i < numbers_size; i++) {
        int current = numbers[i];
        int in_has2 = contains(has2, has2_size, current);
        if (in_has2) {
            continue;
        }
        int in_has1 = contains(has1, has1_size, current);
        if (in_has1) {
            has2[has2_size] = current;
            has2_size = has2_size + 1;
        } else {
            has1[has1_size] = current;
            has1_size = has1_size + 1;
        }
    }

    int output_size = 0;

    for (i = 0; i < numbers_size; i++) {
        int current2 = numbers[i];
        int in_has2_second = contains(has2, has2_size, current2);
        if (!in_has2_second) {
            data[output_size] = current2;
            output_size = output_size + 1;
        }
    }

    out->size = output_size;
    free_int_array(has1, has1_size, numbers_size);
    free_int_array(has2, has2_size, numbers_size);

    return out;
}
