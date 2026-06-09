# P008 Sum product

## Problem (HumanEval 8)

For a given vector of integers, return a vector consisting of a sum && a product of all the integers in a vector.
Empty sum should be equal to 0 && empty product should be equal to 1.
>>> p008_sum_product({})
(0, 1)
>>> p008_sum_product({1, 2, 3, 4})
(10, 24)

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

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
For a given vector of integers, return a vector consisting of a sum && a product of all the integers in a vector.
Empty sum should be equal to 0 && empty product should be equal to 1.
>>> p008_sum_product({})
(0, 1)
>>> p008_sum_product({1, 2, 3, 4})
(10, 24)
*/

int *malloc_int_array(int size)
;

int *p008_sum_product(int *numbers, int numbers_size)

{
    int sum = 0;
    int product = 1;
    int i;
    int *out = malloc_int_array(2);

    for (i = 0; i < numbers_size; i++) {
        sum += numbers[i];
        product *= numbers[i];
    }

    out[0] = sum;
    out[1] = product;
    return out;
}
```
