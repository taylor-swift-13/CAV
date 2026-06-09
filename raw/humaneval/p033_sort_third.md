# P033 Sort third

## Problem (HumanEval 33)

This function takes a vector l && returns a vector l' such that
l' is identical to l in the indicies that are ! divisible by three, while its values at the indicies that are divisible by three are equal
to the values of the corresponding indicies of l, but sorted.
>>> p033_sort_third({1, 2, 3})
{1, 2, 3}
>>> p033_sort_third({5, 6, 3, 4, 8, 9, 2})
{2, 6, 3, 4, 8, 9, 5}

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
This function takes a vector l and returns a vector l' such that l' is
identical to l at indices that are not divisible by three, while the values at
indices divisible by three are the corresponding values of l, but sorted.

>>> p033_sort_third({1, 2, 3})
{1, 2, 3}
>>> p033_sort_third({5, 6, 3, 4, 8, 9, 2})
{2, 6, 3, 4, 8, 9, 5}
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

IntArray *p033_sort_third(int *l, int l_size)

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
```
