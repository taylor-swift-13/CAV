# P145 Order by points

## Problem (HumanEval 145)

Write a function which sorts the given vector of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original vector.

For example:
>>> p145_order_by_points({1, 11, -1, -11, -12}) == {-1, -11, 1, -12, 11}
>>> p145_order_by_points({}) == {}

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
Write a function which sorts the given vector of integers
in ascending order according to the sum of their digits.
Note: if there are several items with similar sum of their digits,
order them based on their index in original vector.

For example:
>>> p145_order_by_points({1, 11, -1, -11, -12}) == {-1, -11, 1, -12, 11}
>>> p145_order_by_points({}) == {}
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

int signed_digit_score(int x)

{
    int t = abs(x);
    int msd = 0;
    int sum = 0;

    while (t >= 10) t /= 10;
    msd = t;
    sum += (x >= 0) ? msd : -msd;
    t = abs(x);
    if (t >= 10) {
        int p = 1;

        while (p * 10 <= t) p *= 10;
        t %= p;
    } else t = 0;

    while (t > 0) {
        sum += t % 10;
        t /= 10;
    }
    return sum;
}

IntArray *p145_order_by_points(int* nums, int nums_size)

{
    IntArray *out = malloc_int_array_struct();
    int* score;
    out->size = nums_size;
    out->data = malloc_int_array(nums_size);
    score = malloc_int_array(nums_size);
    int *data = out->data;
    if (data == 0 || score == 0) {
        out->size = 0;
        return out;
    }
    int i;

    for (i=0;i<nums_size;i++) {
        data[i] = nums[i];
        score[i] = signed_digit_score(nums[i]);

    }

    for (i=0;i<nums_size;i++) {
        int j;

        for (j=1;j<nums_size;j++)
        if (score[j-1]>score[j])
        {
            int m=score[j];score[j]=score[j-1];score[j-1]=m;
            m=data[j];data[j]=data[j-1];data[j-1]=m;
        }

    }

    free_int_array(score, nums_size);
    return out;
}
```
