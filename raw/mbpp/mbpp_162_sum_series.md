# MBPP 162 Sum Series

## Problem

Write a function to calculate the sum (n - 2*i) from i=0 to n // 2, for instance n + (n-2) + (n-4)... (until n-x =< 0).

## Signature

- Python: `sum_series(n: int) -> int`
- C entrypoint: `mbpp_162_sum_series`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum_series(6) == 12`
- `assert sum_series(10) == 30`
- `assert sum_series(9) == 25`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 162.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum_series(n):
  if n < 1:
    return 0
  else:
    return n + sum_series(n - 2)
```

## Reference Implementation

```c
int mbpp_162_sum_series(int n) {
    if ((n < 1)) {
        return 0;
    } else {
        return (n + mbpp_162_sum_series((n - 2)));
    }
}
```
