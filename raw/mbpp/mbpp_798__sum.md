# MBPP 798  Sum

## Problem

Write a python function to find the sum of an array.

## Signature

- Python: `_sum(arr: List[int]) -> int`
- C entrypoint: `mbpp_798__sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert _sum([1, 2, 3]) == 6`
- `assert _sum([15, 12, 13, 10]) == 50`
- `assert _sum([0, 1, 2]) == 3`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 798.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def _sum(arr):  
    sum=0
    for i in arr: 
        sum = sum + i      
    return(sum)
```

## Reference Implementation

```c
int mbpp_798__sum(int *arr, int arr_size) {
    int sum = 0;
    int i;
    for (int __mbpp_i0 = 0; __mbpp_i0 < arr_size; __mbpp_i0++) {
        i = arr[__mbpp_i0];
        sum = (sum + i);
    }
    return sum;
}
```
