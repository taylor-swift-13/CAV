# P034 Unique

## Problem (HumanEval 34)

Return sorted p034_unique elements in a vector
>>> p034_unique({5, 3, 5, 2, 3, 3, 9, 0, 123})
{0, 2, 3, 5, 9, 123}

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
Return sorted p034_unique elements in a vector
>>> p034_unique({5, 3, 5, 2, 3, 3, 9, 0, 123})
{0, 2, 3, 5, 9, 123}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int contains(int *a, int n, int x)

{
    int i;

    for (i = 0; i < n; i++) {
        if (a[i] == x) {
            return 1;
        }
    }
    return 0;
}

void sort_int_array(int *array, int init_size, int size, int ascending)
;

IntArray *p034_unique(int *l, int l_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(l_size);
    int *data = out->data;
    int output_size = 0;
    int i;

    for (i = 0; i < l_size; i++) {
        int current = l[i];
        int in_output = contains(data, output_size, current);
        if (!in_output) {
            data[output_size] = current;
            output_size = output_size + 1;
        }
    }
    sort_int_array(data, output_size, l_size, 1);
    out->size = output_size;
    return out;
}
```
