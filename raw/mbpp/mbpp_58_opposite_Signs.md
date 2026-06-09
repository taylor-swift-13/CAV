# MBPP 58 Opposite Signs

## Problem

Write a python function to check whether the given two integers have opposite sign or not.

## Signature

- Python: `opposite_Signs(x: int, y: int) -> bool`
- C entrypoint: `mbpp_58_opposite_Signs`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert opposite_Signs(1,-2) == True`
- `assert opposite_Signs(3,2) == False`
- `assert opposite_Signs(-10,-10) == False`
- `assert opposite_Signs(-2,2) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 58.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def opposite_Signs(x,y): 
    return ((x ^ y) < 0);
```

## Reference Implementation

```c
int mbpp_58_opposite_Signs(int x, int y) {
    return ((x ^ y) < 0);
}
```
