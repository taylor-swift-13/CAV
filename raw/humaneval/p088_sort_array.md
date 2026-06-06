# P088 Sort array

## Problem (HumanEval 88)

Given a vector of non-negative integers, return a copy of the given vector after sorting,
you will sort the given vector in ascending order if the sum( first index value, last index value) is odd,
|| sort it in descending order if the sum( first index value, last index value) is even.

Note:
* don't change the given vector.

Examples:
* sort_vector({}) => {}
* sort_vector({5}) => {5}
* sort_vector({2, 4, 3, 0, 1, 5}) => {0, 1, 2, 3, 4, 5}
* sort_vector({2, 4, 3, 0, 1, 5, 6}) => {6, 5, 4, 3, 2, 1, 0}

## Reference Implementation

```c
/*
Given a vector of non-negative integers, return a copy of the given vector after sorting,
you will sort the given vector in ascending order if the sum( first index value, last index value) is odd,
|| sort it in descending order if the sum( first index value, last index value) is even.

Note:
* don't change the given vector.

Examples:
* sort_vector({}) => {}
* sort_vector({5}) => {5}
* sort_vector({2, 4, 3, 0, 1, 5}) => {0, 1, 2, 3, 4, 5}
* sort_vector({2, 4, 3, 0, 1, 5, 6}) => {6, 5, 4, 3, 2, 1, 0}
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

void sort_int_array(int *array, int size)
;

IntArray *p088_sort_array(int *array, int array_size)

{
    IntArray *out = malloc_int_array_struct();
    out->size = array_size;
    out->data = malloc_int_array(array_size);
    int *data = out->data;
    int i;
    int t = 0;

    if (array_size == 0) {
        return out;
    }

    for (i = 0; i < array_size; i++) {
        data[i] = array[i];
    }

    sort_int_array(data, array_size);

    if ((array[0] + array[array_size - 1]) % 2 == 0)
    {

        for (i = 0; i < array_size / 2; i++) {
            t = data[i];
            data[i] = data[array_size - 1 - i];
            data[array_size - 1 - i] = t;
        }
    }
    return out;
}
```
