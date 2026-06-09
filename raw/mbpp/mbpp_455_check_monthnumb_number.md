# MBPP 455 Check Monthnumb Number

## Problem

Write a function to check whether the given month number contains 31 days or not.

## Signature

- Python: `check_monthnumb_number(monthnum2: int) -> bool`
- C entrypoint: `mbpp_455_check_monthnumb_number`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert check_monthnumb_number(5)==True`
- `assert check_monthnumb_number(2)==False`
- `assert check_monthnumb_number(6)==False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 455.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def check_monthnumb_number(monthnum2):
  if(monthnum2==1 or monthnum2==3 or monthnum2==5 or monthnum2==7 or monthnum2==8 or monthnum2==10 or monthnum2==12):
    return True
  else:
    return False
```

## Reference Implementation

```c
int mbpp_455_check_monthnumb_number(int monthnum2) {
    if (((monthnum2 == 1) || (monthnum2 == 3) || (monthnum2 == 5) || (monthnum2 == 7) || (monthnum2 == 8) || (monthnum2 == 10) || (monthnum2 == 12))) {
        return 1;
    } else {
        return 0;
    }
}
```
