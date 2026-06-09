# P025 Factorize

## Problem (HumanEval 25)

Return vector of prime factors of given integer in the order from smallest to largest.
Each of the factors should be vectored number of times corresponding to how many times it appeares in factorization.
Input number should be equal to the product of all factors
>>> p025_factorize(8)
{2, 2, 2}
>>> p025_factorize(25)
{5, 5}
>>> p025_factorize(70)
{2, 5, 7}

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
Return a pointer to a newly allocated IntArray containing the prime factors of
given integer in the order from smallest to largest.
Each of the factors should be vectored number of times corresponding to how many times it appeares in factorization.
Input number should be equal to the product of all factors
>>> p025_factorize(8)
{2, 2, 2}
>>> p025_factorize(25)
{5, 5}
>>> p025_factorize(70)
{2, 5, 7}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p025_factorize(int n)

{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(n);
    int *data = out->data;

    for (int i=2;i<=n/i;i++)
        if (n%i==0)
        {
            n=n/i;
            data[out->size] = i;
            out->size = out->size + 1;
            i-=1;
        }
    data[out->size] = n;
    out->size = out->size + 1;
    return out;
}
```
