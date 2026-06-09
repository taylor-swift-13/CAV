# MBPP 170 Sum Range List

## Problem

Write a function to find the sum of numbers in a list within a range specified by two indices.

## Signature

- Python: `sum_range_list(list1: List[int], m: int, n: int) -> int`
- C entrypoint: `mbpp_170_sum_range_list`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum_range_list([2,1,5,6,8,3,4,9,10,11,8,12], 8, 10) == 29`
- `assert sum_range_list([2,1,5,6,8,3,4,9,10,11,8,12], 5, 7) == 16`
- `assert sum_range_list([2,1,5,6,8,3,4,9,10,11,8,12], 7, 10) == 38`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 170.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum_range_list(list1, m, n):                                                                                                                                                                                                
    sum_range = 0                                                                                                                                                                                                         
    for i in range(m, n+1, 1):                                                                                                                                                                                        
        sum_range += list1[i]                                                                                                                                                                                                  
    return sum_range
```

## Reference Implementation

```c
int mbpp_170_sum_range_list(int *list1, int list1_size, int m, int n) {
    int sum_range = 0;
    int i;
    for (i = m; i < (n + 1); i++) {
        sum_range += list1[i];
    }
    return sum_range;
}
```
