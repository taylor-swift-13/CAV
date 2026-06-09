# MBPP 793 Last

## Problem

Write a python function to find the last position of an element in a sorted array.

## Signature

- Python: `last(arr: List[int], x: int) -> int`
- C entrypoint: `mbpp_793_last`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert last([1,2,3],1) == 0`
- `assert last([1,1,1,2,3,4],1) == 2`
- `assert last([2,3,2,3,6,8,9],3) == 3`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 793.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def last(arr,x):
    n = len(arr)
    low = 0
    high = n - 1
    res = -1  
    while (low <= high):
        mid = (low + high) // 2 
        if arr[mid] > x:
            high = mid - 1
        elif arr[mid] < x:
            low = mid + 1
        else:
            res = mid
            low = mid + 1
    return res
```

## Reference Implementation

```c
int mbpp_793_last(int *arr, int arr_size, int x) {
    int n = arr_size;
    int low = 0;
    int high = (n - 1);
    int res = (-1);
    while ((low <= high)) {
        int mid = ((low + high) / 2);
        if ((arr[mid] > x)) {
            high = (mid - 1);
        } else {
            if ((arr[mid] < x)) {
                low = (mid + 1);
            } else {
                res = mid;
                low = (mid + 1);
            }
        }
    }
    return res;
}
```
