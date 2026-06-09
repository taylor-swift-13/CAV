# P155 Even odd count

## Problem (HumanEval 155)

Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    p155_even_odd_count(-12) ==> {1, 1}
    p155_even_odd_count(123) ==> {1, 2}

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

### `abs`

Coq model:

```coq
Definition he_abs_spec (x r : Z) : Prop :=
  r = Z.abs x.
```

Contract shape:

```c
int abs(int x)
/*@ Require INT_MIN < x && x <= INT_MAX
    Ensure he_abs_spec(x, __return)
*/;
```

## Reference Implementation

```c
/*
Given an integer. return a vector that has the number of even && odd digits respectively.

 Example:
    p155_even_odd_count(-12) ==> {1, 1}
    p155_even_odd_count(123) ==> {1, 2}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

IntArray *p155_even_odd_count(int num)

{
    int w = abs(num);
    int n1=0,n2=0;
    int d=0;
    if (w == 0) n2 = 1;

    while (w > 0) {
        d = w % 10;
        if (d % 2 == 1) {
            n1 += 1;

        } else {
            n2 += 1;

        }
        w /= 10;
    }
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = n2;
    data[1] = n1;
    return out;
}
```
