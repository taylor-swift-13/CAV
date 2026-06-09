# MBPP 145 Max Abs Diff

## Problem

Write a python function to find the maximum difference between any two elements in a given array.

## Signature

- Python: `max_Abs_Diff(arr: List[int]) -> int`
- C entrypoint: `mbpp_145_max_Abs_Diff`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert max_Abs_Diff((2,1,5,3)) == 4`
- `assert max_Abs_Diff((9,3,2,5,1)) == 8`
- `assert max_Abs_Diff((3,2,1)) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 145.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def max_Abs_Diff(arr): 
    n = len(arr)
    minEle = arr[0] 
    maxEle = arr[0] 
    for i in range(1, n): 
        minEle = min(minEle,arr[i]) 
        maxEle = max(maxEle,arr[i]) 
    return (maxEle - minEle)
```

## Reference Implementation

```c
static int __mbpp_max_int(int a, int b) {
    if (a > b) {
        return a;
    }
    return b;
}

static int __mbpp_min_int(int a, int b) {
    if (a < b) {
        return a;
    }
    return b;
}

int mbpp_145_max_Abs_Diff(int *arr, int arr_size) {
    int n = arr_size;
    int minEle = arr[0];
    int maxEle = arr[0];
    int i;
    for (i = 1; i < n; i++) {
        minEle = __mbpp_min_int(minEle, arr[i]);
        maxEle = __mbpp_max_int(maxEle, arr[i]);
    }
    return (maxEle - minEle);
}
```
