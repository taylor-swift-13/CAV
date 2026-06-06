# P070 Strange sort list

## Problem (HumanEval 70)

Given vector of integers, return vector in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum && so on.

Examples:
strange_sort_vector({1, 2, 3, 4}) == {1, 4, 2, 3}
strange_sort_vector({5, 5, 5, 5}) == {5, 5, 5, 5}
strange_sort_vector({}) == {}

## Reference Implementation

```c
/*
Given vector of integers, return vector in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum && so on.

Examples:
strange_sort_vector({1, 2, 3, 4}) == {1, 4, 2, 3}
strange_sort_vector({5, 5, 5, 5}) == {5, 5, 5, 5}
strange_sort_vector({}) == {}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

void free_int_array(int *array, int size)
;

void sort_int_array(int *array, int init_size, int size, int ascending)
;

IntArray *p070_strange_sort_list(int *lst, int lst_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = lst_size;
    out->data = malloc_int_array(lst_size);
    int *data = out->data;
    int *sorted = malloc_int_array(lst_size);
    int i;

    for (i = 0; i < lst_size; i++) {
        sorted[i] = lst[i];
    }

    sort_int_array(sorted, lst_size, lst_size, 1);

    for (i = 0; i < lst_size; i++) {
        if (i % 2 == 0) {
            data[i] = sorted[i / 2];
        } else {
            data[i] = sorted[lst_size - 1 - (i / 2)];
        }
    }

    free_int_array(sorted, lst_size);
    return out;
}
```
