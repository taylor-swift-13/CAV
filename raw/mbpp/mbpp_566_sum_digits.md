# MBPP 566 Sum Digits

## Problem

Write a function to get the sum of the digits of a non-negative integer.

## Signature

- Python: `sum_digits(n: int) -> int`
- C entrypoint: `mbpp_566_sum_digits`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum_digits(345)==12`
- `assert sum_digits(12)==3`
- `assert sum_digits(97)==16`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 566.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum_digits(n):
  if n == 0:
    return 0
  else:
    return n % 10 + sum_digits(int(n / 10))
```

## Reference Implementation

```c
int mbpp_566_sum_digits(int n) {
    if ((n == 0)) {
        return 0;
    } else {
        return ((n % 10) + mbpp_566_sum_digits(((int)((n / 10)))));
    }
}
```
