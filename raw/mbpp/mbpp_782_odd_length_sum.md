# MBPP 782 Odd Length Sum

## Problem

Write a python function to find the sum of all odd length subarrays. https://www.geeksforgeeks.org/sum-of-all-odd-length-subarrays/

## Signature

- Python: `odd_length_sum(arr: List[int]) -> int`
- C entrypoint: `mbpp_782_odd_length_sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert odd_length_sum([1,2,4]) == 14`
- `assert odd_length_sum([1,2,1,2]) == 15`
- `assert odd_length_sum([1,7]) == 8`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 782.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def odd_length_sum(arr):
    Sum = 0
    l = len(arr)
    for i in range(l):
        Sum += ((((i + 1) *(l - i) + 1) // 2) * arr[i])
    return Sum
```

## Reference Implementation

```c
int mbpp_782_odd_length_sum(int *arr, int arr_size) {
    int Sum = 0;
    int l = arr_size;
    int i;
    for (i = 0; i < l; i++) {
        Sum += (((((i + 1) * (l - i)) + 1) / 2) * arr[i]);
    }
    return Sum;
}
```
