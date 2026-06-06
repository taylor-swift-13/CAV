# P120 Maximum

## Problem (HumanEval 120)

Given a vector arr of integers && a positive integer k, return a sorted vector
of length k with the p120_maximum k numbers in arr.

Example 1:

    Input: arr = {-3, -4, 5}, k = 3
    Output: {-4, -3, 5}

Example 2:

    Input: arr = {4, -4, 4}, k = 2
    Output: {4, 4}

Example 3:

    Input: arr = {-3, 2, 1, 2, -1, -2, 1}, k = 1
    Output: {2}

Note:
    1. The length of the vector will be in the range of {1, 1000}.
    2. The elements in the vector will be in the range of {-1000, 1000}.
    3. 0 <= k <= len(arr)

## Reference Implementation

```c
/*
Given a vector arr of integers && a positive integer k, return a sorted vector
of length k with the p120_maximum k numbers in arr.

Example 1:

    Input: arr = {-3, -4, 5}, k = 3
    Output: {-4, -3, 5}

Example 2:

    Input: arr = {4, -4, 4}, k = 2
    Output: {4, 4}

Example 3:

    Input: arr = {-3, 2, 1, 2, -1, -2, 1}, k = 1
    Output: {2}

Note:
    1. The length of the vector will be in the range of {1, 1000}.
    2. The elements in the vector will be in the range of {-1000, 1000}.
    3. 0 <= k <= len(arr)
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

IntArray *p120_maximum(int *arr, int arr_size, int k)

{
    IntArray *out = malloc_int_array_struct();
    out->data = 0;
    out->size = 0;

    if (k <= 0) {
        out->data = malloc_int_array(0);
        out->size = 0;
        return out;
    }

    int *tmp = malloc_int_array(arr_size);
    int i;

    for (i = 0; i < arr_size; i++) {
        tmp[i] = arr[i];
    }

    sort_int_array(tmp, arr_size, arr_size, 1);

    out->data = malloc_int_array(k);
    int *data = out->data;

    for (i = 0; i < k; i++) {
        data[i] = tmp[arr_size - k + i];
    }

    out->size = k;
    free_int_array(tmp, arr_size);
    return out;
}
```
