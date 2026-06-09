# P116 Sort array

## Problem (HumanEval 116)

In this Kata, you have to sort a vector of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_vector({1, 5, 2, 3, 4}) == {1, 2, 3, 4, 5}
>>> sort_vector({-2, -3, -4, -5, -6}) == {-6, -5, -4, -3, -2}
>>> sort_vector({1, 0, 2, 3, 4}) == {0, 1, 2, 3, 4}

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
In this Kata, you have to sort a vector of non-negative integers according to
number of ones in their binary representation in ascending order.
For similar number of ones, sort based on decimal value.

It must be implemented like this:
>>> sort_vector({1, 5, 2, 3, 4}) == {1, 2, 3, 4, 5}
>>> sort_vector({-2, -3, -4, -5, -6}) == {-6, -5, -4, -3, -2}
>>> sort_vector({1, 0, 2, 3, 4}) == {0, 1, 2, 3, 4}
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

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

IntArray *p116_sort_array(int* arr, int arr_size)

{
    IntArray *out = malloc_int_array_struct();
    int* bin = 0;
    int m = 0;

    out->size = arr_size;
    out->data = malloc_int_array(arr_size);
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    int i;

    for (i = 0; i < arr_size; i++) {
        data[i] = arr[i];

    }

    bin = malloc_int_array(arr_size);
    if (bin == 0) {
        free_int_array(data, arr_size);
        out->data = 0;
        out->size = 0;
        return out;
    }

    for (i=0;i<arr_size;i++)
    {
        int b = 0;
        int n = 0;

        n = out->data[i];
        n = abs(n);
        b = 0;

        while (n>0)
        {
            b+=n%2;n=n/2;
        }
        bin[i] = b;

    }

    for (i=0;i<arr_size;i++)
    {
        int j;

        for (j=1;j<arr_size;j++)
        if (bin[j]<bin[j-1] || (bin[j]==bin[j-1] && data[j]<data[j-1]))
        {
            m=out->data[j];out->data[j]=out->data[j-1];out->data[j-1]=m;
            m=bin[j];bin[j]=bin[j-1];bin[j-1]=m;
        }

    }

    free_int_array(bin, arr_size);
    return out;
}
```
