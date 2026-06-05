# Can Arrange 135

## Problem (HumanEval 135)

Create a function which returns the largest index of an element which
is ! greater than || equal to the element immediately preceding it. If
no such element exists then return -1. The given vector will ! contain
duplicate values.

Examples:
can_arrange_135({1,2,4,3,5}) = 3
can_arrange_135({1,2,3}) = -1

## Reference Implementation

```c
int can_arrange_135(int* arr, int arr_size){
    int max=-1;
    for (int i=0;i<arr_size;i++)
    if (arr[i]<=i) max=i;
    return max;
}
```
