# P100 Make a pile

## Problem (HumanEval 100)

Given a positive integer n, you have to make a pile of n levels of stones.
The first level has n stones.
The number of stones in the next level is:
    - the next odd number if n is odd.
    - the next even number if n is even.
Return the number of stones in each level in a vector, where element at index
i represents the number of stones in the level (i+1).

Examples:
>>> p100_make_a_pile(3)
{3, 5, 7}

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

## Reference Implementation

```c
/*
Given a positive integer n, make a pile of n levels of stones.
Level i (0-indexed) has n + 2*i stones (always increments by 2).

>>> p100_make_a_pile(3) => {3, 5, 7}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p100_make_a_pile(int n)

{
    IntArray *out = malloc_int_array_struct();
    out->size = n;
    out->data = malloc_int_array(n);
    int *data = out->data;
    int i;

    for (i = 0; i < n; i++)
        data[i] = n + 2 * i;
    return out;
}
```
