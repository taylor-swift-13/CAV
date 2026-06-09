# MBPP 77 Is Diff

## Problem

Write a python function to find whether a number is divisible by 11.

## Signature

- Python: `is_Diff(n: int) -> bool`
- C entrypoint: `mbpp_77_is_Diff`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_Diff (12345) == False`
- `assert is_Diff(1212112) == True`
- `assert is_Diff(1212) == False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 77.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_Diff(n): 
    return (n % 11 == 0)
```

## Reference Implementation

```c
int mbpp_77_is_Diff(int n) {
    return ((n % 11) == 0);
}
```
