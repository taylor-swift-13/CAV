# MBPP 734 Sum Of Subarray Prod

## Problem

Write a python function to find sum of products of all possible sublists of a given list. https://www.geeksforgeeks.org/sum-of-products-of-all-possible-subarrays/

## Signature

- Python: `sum_Of_Subarray_Prod(arr: List[int]) -> int`
- C entrypoint: `mbpp_734_sum_Of_Subarray_Prod`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum_Of_Subarray_Prod([1,2,3]) == 20`
- `assert sum_Of_Subarray_Prod([1,2]) == 5`
- `assert sum_Of_Subarray_Prod([1,2,3,4]) == 84`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 734.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum_Of_Subarray_Prod(arr):
    ans = 0
    res = 0
    i = len(arr) - 1
    while (i >= 0):
        incr = arr[i]*(1 + res)
        ans += incr
        res = incr
        i -= 1
    return (ans)
```

## Reference Implementation

```c
int mbpp_734_sum_Of_Subarray_Prod(int *arr, int arr_size) {
    int ans = 0;
    int res = 0;
    int i = (arr_size - 1);
    while ((i >= 0)) {
        int incr = (arr[i] * (1 + res));
        ans += incr;
        res = incr;
        i -= 1;
    }
    return ans;
}
```
