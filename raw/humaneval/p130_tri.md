# P130 Tri

## Problem (HumanEval 130)

Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
p130_tri(1) = 3
p130_tri(n) = 1 + n / 2, if n is even.
p130_tri(n) =  p130_tri(n - 1) + p130_tri(n - 2) + p130_tri(n + 1), if n is odd.
For example:
p130_tri(2) = 1 + (2 / 2) = 2
p130_tri(4) = 3
p130_tri(3) = p130_tri(2) + p130_tri(1) + p130_tri(4)
       = 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a vector of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
p130_tri(3) = {1, 3, 2, 8}

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
Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in
the last couple centuries. However, what people don't know is Tribonacci sequence.
Tribonacci sequence is defined by the recurrence:
p130_tri(1) = 3
p130_tri(n) = 1 + n / 2, if n is even.
p130_tri(n) =  p130_tri(n - 1) + p130_tri(n - 2) + p130_tri(n + 1), if n is odd.
For example:
p130_tri(2) = 1 + (2 / 2) = 2
p130_tri(4) = 3
p130_tri(3) = p130_tri(2) + p130_tri(1) + p130_tri(4)
       = 2 + 3 + 3 = 8
You are given a non-negative integer number n, you have to a return a vector of the
first n + 1 numbers of the Tribonacci sequence.
Examples:
p130_tri(3) = {1, 3, 2, 8}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p130_tri(int n)

{
    IntArray *out = malloc_int_array_struct();
    out->size = n + 1;
    out->data = malloc_int_array(n + 1);
    int *data = out->data;
    data[0] = 1;
    if (n == 0) return out;
    data[1] = 3;
    int i;

    for (i = 2; i <= n; i++)
    {
        if (i % 2 == 0) data[i] = 1 + i / 2;
        else data[i] = data[i - 1] + data[i - 2] + 1 + (i + 1) / 2;
    }
    return out;
}
```
