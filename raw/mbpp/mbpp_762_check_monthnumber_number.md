# MBPP 762 Check Monthnumber Number

## Problem

Write a function to check whether the given month number contains 30 days or not. Months are given as number from 1 to 12.

## Signature

- Python: `check_monthnumber_number(monthnum3: int) -> bool`
- C entrypoint: `mbpp_762_check_monthnumber_number`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert check_monthnumber_number(6)==True`
- `assert check_monthnumber_number(2)==False`
- `assert check_monthnumber_number(12)==False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 762.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def check_monthnumber_number(monthnum3):
  return monthnum3==4 or monthnum3==6 or monthnum3==9 or monthnum3==11
```

## Reference Implementation

```c
int mbpp_762_check_monthnumber_number(int monthnum3) {
    return ((monthnum3 == 4) || (monthnum3 == 6) || (monthnum3 == 9) || (monthnum3 == 11));
}
```
