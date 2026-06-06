# P073 Smallest change

## Problem (HumanEval 73)

Given a vector arr of integers, find the minimum number of elements that
need to be changed to make the vector palindromic. A palindromic vector is a vector that
is read the same backwards && forwards. In one change, you can change one element to any other element.

For example:
p073_smallest_change({1,2,3,5,4,7,9,6}) == 4
p073_smallest_change({1, 2, 3, 4, 3, 2, 2}) == 1
p073_smallest_change({1, 2, 3, 2, 1}) == 0

## Reference Implementation

```c
/*
Given a vector arr of integers, find the minimum number of elements that
need to be changed to make the vector palindromic. A palindromic vector is a vector that
is read the same backwards && forwards. In one change, you can change one element to any other element.

For example:
p073_smallest_change({1,2,3,5,4,7,9,6}) == 4
p073_smallest_change({1, 2, 3, 4, 3, 2, 2}) == 1
p073_smallest_change({1, 2, 3, 2, 1}) == 0
*/

int p073_smallest_change(int *arr, int arr_size)

{
    int out = 0;
    int i;

    for (i = 0; i < arr_size - 1 - i; i++)
        if (arr[i] != arr[arr_size - 1 - i])
            out += 1;
    return out;
}
```
