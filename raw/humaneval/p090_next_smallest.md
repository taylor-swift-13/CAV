# P090 Next smallest

## Problem (HumanEval 90)

You are given a vector of integers.
Write a function p090_next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

p090_next_smallest({1, 2, 3, 4, 5}) == 2
p090_next_smallest({5, 1, 4, 3, 2}) == 2
p090_next_smallest({}) == None
p090_next_smallest({1, 1}) == None

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

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
You are given a vector of integers.
Write a function p090_next_smallest() that returns the 2nd smallest element of the vector.
Return None if there is no such element.

p090_next_smallest({1, 2, 3, 4, 5}) == 2
p090_next_smallest({5, 1, 4, 3, 2}) == 2
p090_next_smallest({}) == None
p090_next_smallest({1, 1}) == None
*/

void sort_int_array(int *array, int init_size, int size, int ascending)
;

int p090_next_smallest(int *lst, int lst_size)

{
    int i;

    if (lst_size <= 1) {
        return -1;
    }

    sort_int_array(lst, lst_size, lst_size, 1);

    for (i = 1; i < lst_size; i++) {
        if (lst[i] != lst[i - 1]) {
            return lst[i];
        }
    }
    return -1;
}
```
