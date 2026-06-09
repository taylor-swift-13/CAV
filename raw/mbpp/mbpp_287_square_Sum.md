# MBPP 287 Square Sum

## Problem

Write a python function takes in an integer n and returns the sum of squares of first n even natural numbers.

## Signature

- Python: `square_Sum(n: int) -> int`
- C entrypoint: `mbpp_287_square_Sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert square_Sum(2) == 20`
- `assert square_Sum(3) == 56`
- `assert square_Sum(4) == 120`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 287.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def square_Sum(n):  
    return int(2*n*(n+1)*(2*n+1)/3)
```

## Reference Implementation

```c
int mbpp_287_square_Sum(int n) {
    return ((int)(((((2 * n) * (n + 1)) * ((2 * n) + 1)) / 3)));
}
```
