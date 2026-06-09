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

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `malloc_int_array_struct`

Allocates a fresh `IntArray` header object.

Contract shape:

```c
IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;
```

### `malloc_int_array`

Allocates a fresh writable integer array with unspecified contents.

Contract shape:

```c
int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;
```

### `free_int_array`

Consumes ownership of a previously allocated integer array.

Contract shape:

```c
void free_int_array(int *array, int size)
/*@ With l
    Require size >= 0 && Zlength(l) == size &&
            IntArray::full(array, size, l)
    Ensure emp
*/;
```

### `sort_int_array`

Coq model: define a relation stating that the output list is sorted in the requested direction and is a permutation of the input list.

Contract shape:

```c
void sort_int_array(int *array, int init_size, int size, int ascending)
/*@ With l
    Require 0 <= size && size <= init_size && Zlength(l) == init_size &&
            IntArray::full(array, init_size, l)
    Ensure exists out_l,
           sort_int_array_spec(l, size, ascending, out_l) &&
           IntArray::full(array, init_size, out_l)
*/;
```

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
