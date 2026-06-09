# P163 Generate integers

## Problem (HumanEval 163)

Given two positive integers a && b, return the even digits between a
&& b, in ascending order.

For example:
p163_generate_integers(2, 8) => {2, 4, 6, 8}
p163_generate_integers(8, 2) => {2, 4, 6, 8}
p163_generate_integers(10, 14) => {}

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
Given two positive integers a && b, return the even digits between a
&& b, in ascending order.

For example:
p163_generate_integers(2, 8) => {2, 4, 6, 8}
p163_generate_integers(8, 2) => {2, 4, 6, 8}
p163_generate_integers(10, 14) => {}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p163_generate_integers(int a,int b)

{
    int m = 0;
    IntArray *out = malloc_int_array_struct();
    out->data = (void *)0;
    out->size = 0;
    if (b<a)
    {
        m=a;a=b;b=m;
    }

    int capacity = 10;
    out->data = malloc_int_array(capacity);
    int *data = out->data;
    if (data == 0) {
        return out;
    }
    int output_size = out->size;
    int i;

    for (i=a;i<=b;i++) {
        if (i<10 && i%2==0) {

            data[output_size] = i;
            output_size++;

        }

    }
    out->size = output_size;

    return out;
}
```
