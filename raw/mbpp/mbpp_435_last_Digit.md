# MBPP 435 Last Digit

## Problem

Write a python function to find the last digit of a given number.

## Signature

- Python: `last_Digit(n: int) -> int`
- C entrypoint: `mbpp_435_last_Digit`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert last_Digit(123) == 3`
- `assert last_Digit(25) == 5`
- `assert last_Digit(30) == 0`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 435.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def last_Digit(n) :
    return (n % 10)
```

## Reference Implementation

```c
int mbpp_435_last_Digit(int n) {
    return (n % 10);
}
```
