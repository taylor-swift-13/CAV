# MBPP 600 Is Even

## Problem

Write a python function to check whether the given number is even or not.

## Signature

- Python: `is_Even(n: int) -> bool`
- C entrypoint: `mbpp_600_is_Even`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_Even(1) == False`
- `assert is_Even(2) == True`
- `assert is_Even(3) == False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 600.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_Even(n) : 
    if (n^1 == n+1) :
        return True; 
    else :
        return False;
```

## Reference Implementation

```c
int mbpp_600_is_Even(int n) {
    if (((n ^ 1) == (n + 1))) {
        return 1;
    } else {
        return 0;
    }
}
```
