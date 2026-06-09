# P070 Strange sort list

## Problem (HumanEval 70)

Given vector of integers, return vector in strange order.
Strange sorting, is when you start with the minimum value,
then maximum of the remaining integers, then minimum && so on.

Examples:
strange_sort_vector({1, 2, 3, 4}) == {1, 4, 2, 3}
strange_sort_vector({5, 5, 5, 5}) == {5, 5, 5, 5}
strange_sort_vector({}) == {}

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
