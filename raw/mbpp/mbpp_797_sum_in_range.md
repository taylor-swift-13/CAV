# MBPP 797 Sum In Range

## Problem

Write a python function to find the sum of all odd natural numbers within the range l and r.

## Signature

- Python: `sum_in_range(l: int, r: int) -> int`
- C entrypoint: `mbpp_797_sum_in_range`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum_in_range(2,5) == 8`
- `assert sum_in_range(5,7) == 12`
- `assert sum_in_range(7,13) == 40`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 797.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum_odd(n): 
    terms = (n + 1)//2
    sum1 = terms * terms 
    return sum1  
def sum_in_range(l,r): 
    return sum_odd(r) - sum_odd(l - 1)
```

## Reference Implementation

```c
int sum_odd(int n) {
    int terms = ((n + 1) / 2);
    int sum1 = (terms * terms);
    return sum1;
}

int mbpp_797_sum_in_range(int l, int r) {
    return (sum_odd(r) - sum_odd((l - 1)));
}
```
