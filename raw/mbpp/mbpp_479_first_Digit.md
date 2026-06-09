# MBPP 479 First Digit

## Problem

Write a python function to find the first digit of a given number.

## Signature

- Python: `first_Digit(n: int) -> int`
- C entrypoint: `mbpp_479_first_Digit`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert first_Digit(123) == 1`
- `assert first_Digit(456) == 4`
- `assert first_Digit(12) == 1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 479.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def first_Digit(n) :  
    while n >= 10:  
        n = n / 10 
    return int(n)
```

## Reference Implementation

```c
int mbpp_479_first_Digit(int n) {
    while ((n >= 10)) {
        n = (n / 10);
    }
    return ((int)(n));
}
```
