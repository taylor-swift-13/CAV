# MBPP 443 Largest Neg

## Problem

Write a python function to find the largest negative number from the given list.

## Signature

- Python: `largest_neg(list1: List[int]) -> int`
- C entrypoint: `mbpp_443_largest_neg`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert largest_neg([1,2,3,-4,-6]) == -6`
- `assert largest_neg([1,2,3,-8,-9]) == -9`
- `assert largest_neg([1,2,3,4,-1]) == -1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 443.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def largest_neg(list1): 
    max = list1[0] 
    for x in list1: 
        if x < max : 
             max = x  
    return max
```

## Reference Implementation

```c
int mbpp_443_largest_neg(int *list1, int list1_size) {
    int max = list1[0];
    int x;
    for (int __mbpp_i0 = 0; __mbpp_i0 < list1_size; __mbpp_i0++) {
        x = list1[__mbpp_i0];
        if ((x < max)) {
            max = x;
        }
    }
    return max;
}
```
