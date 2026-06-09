# P104 Unique digits

## Problem (HumanEval 104)

Given a vector of positive integers x. return a sorted vector of all
elements that hasn't any even digit.

Note: Returned vector should be sorted in increasing order.

For example:
>>> p104_unique_digits({15, 33, 1422, 1})
{1, 15, 33}
>>> p104_unique_digits({152, 323, 1422, 10})
{}

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
Given a vector of positive integers x. return a sorted vector of all
elements that hasn't any even digit.

Note: Returned vector should be sorted in increasing order.

For example:
>>> p104_unique_digits({15, 33, 1422, 1})
{1, 15, 33}
>>> p104_unique_digits({152, 323, 1422, 10})
{}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

void sort_int_array(int *array, int init_size, int size, int ascending)
;

int has_only_odd_digits_int(int value)

{
    int num = value;
    int u = 1;
    if (num == 0) {
        u = 0;
    }

    while (num > 0 && u) {
        if (num % 2 == 0) {
            u = 0;
        }
        num = num / 10;
    }
    return u;
}

IntArray *p104_unique_digits(int *x, int x_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(x_size);
    int *data = out->data;
    int output_size = 0;
    int i;

    for (i = 0; i < x_size; i++) {
        int current = x[i];
        int u = has_only_odd_digits_int(current);
        if (u) {
            data[output_size] = current;
            output_size = output_size + 1;
        }
    }

    sort_int_array(data, output_size, x_size, 1);

    out->size = output_size;
    return out;
}
```
