# P026 Remove duplicates

## Problem (HumanEval 26)

From a vector of integers, remove all elements that occur more than once.
Keep order of elements left the same as in the input.
>>> p026_remove_duplicates({1, 2, 3, 2, 4})
{1, 3, 4}

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

## Reference Implementation

```c
/*
From a vector of integers, remove all elements that occur more than once.
Keep order of elements left the same as in the input.
>>> p026_remove_duplicates({1, 2, 3, 2, 4})
{1, 3, 4}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

void free_int_array(int *array, int init_size, int size)
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

IntArray *p026_remove_duplicates(int *numbers, int numbers_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(numbers_size);
    int *data = out->data;
    int *has1 = malloc_int_array(numbers_size);
    int has1_size = 0;
    int *has2 = malloc_int_array(numbers_size);
    int has2_size = 0;
    int i;

    for (i = 0; i < numbers_size; i++) {
        int current = numbers[i];
        int in_has2 = contains(has2, has2_size, current);
        if (in_has2) {
            continue;
        }
        int in_has1 = contains(has1, has1_size, current);
        if (in_has1) {
            has2[has2_size] = current;
            has2_size = has2_size + 1;
        } else {
            has1[has1_size] = current;
            has1_size = has1_size + 1;
        }
    }

    int output_size = 0;

    for (i = 0; i < numbers_size; i++) {
        int current2 = numbers[i];
        int in_has2_second = contains(has2, has2_size, current2);
        if (!in_has2_second) {
            data[output_size] = current2;
            output_size = output_size + 1;
        }
    }

    out->size = output_size;
    free_int_array(has1, has1_size, numbers_size);
    free_int_array(has2, has2_size, numbers_size);

    return out;
}
```
