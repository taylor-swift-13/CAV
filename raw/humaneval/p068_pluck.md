# P068 Pluck

## Problem (HumanEval 68)

Given a vector representing a branch of a tree that has non-negative integer nodes
your task is to p068_pluck one of the nodes && return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a vector, { smalest_value, its index },
If there are no even values || the given vector is empty, return {}.

Example 1:
    Input: {4,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index.

Example 2:
    Input: {1,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index.

Example 3:
    Input: {}
    Output: {}

Example 4:
    Input: {5, 0, 3, 0, 4, 2}
    Output: {0, 1}
    Explanation: 0 is the smallest value, but  there are two zeros,
                 so we will choose the first zero, which has the smallest index.

Constraints:
    * 1 <= nodes.length <= 10000
    * 0 <= node.value

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
Given a vector representing a branch of a tree that has non-negative integer nodes
your task is to p068_pluck one of the nodes && return it.
The plucked node should be the node with the smallest even value.
If multiple nodes with the same smallest even value are found return the node that has smallest index.

The plucked node should be returned in a vector, { smalest_value, its index },
If there are no even values || the given vector is empty, return {}.

Example 1:
    Input: {4,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index.

Example 2:
    Input: {1,2,3}
    Output: {2, 1}
    Explanation: 2 has the smallest even value, && 2 has the smallest index.

Example 3:
    Input: {}
    Output: {}

Example 4:
    Input: {5, 0, 3, 0, 4, 2}
    Output: {0, 1}
    Explanation: 0 is the smallest value, but  there are two zeros,
                 so we will choose the first zero, which has the smallest index.

Constraints:
    * 1 <= nodes.length <= 10000
    * 0 <= node.value
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p068_pluck(int *arr, int arr_size)

{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 0;
    int *data = out->data;
    int i;

    for (i = 0; i < arr_size; i++) {
        if (arr[i] % 2 == 0 && (out->size == 0 || arr[i] < data[0])) {
            data[0] = arr[i];
            data[1] = i;
            out->size = 2;
        }
    }

    return out;
}
```
