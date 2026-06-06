# P135 Can arrange

## Problem (HumanEval 135)

Create a function which returns the largest index of an element which
is ! greater than || equal to the element immediately preceding it. If
no such element exists then return -1. The given vector will ! contain
duplicate values.

Examples:
p135_can_arrange({1,2,4,3,5}) = 3
p135_can_arrange({1,2,3}) = -1

## Reference Implementation

```c
/*
Create a function which returns the largest index of an element which
is ! greater than || equal to the element immediately preceding it. If
no such element exists then return -1. The given vector will ! contain
duplicate values.

Examples:
p135_can_arrange({1,2,4,3,5}) = 3
p135_can_arrange({1,2,3}) = -1
*/

int p135_can_arrange(int* arr, int arr_size)

{
    int max = -1;
    int i;

    for (i = 0; i < arr_size; i++)
        if (arr[i] <= i) max = i;
    return max;
}
```
