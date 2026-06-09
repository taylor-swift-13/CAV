# MBPP 14 Find Volume

## Problem

Write a python function to find the volume of a triangular prism.

## Signature

- Python: `find_Volume(l: int, b: int, h: int) -> int`
- C entrypoint: `mbpp_14_find_Volume`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_Volume(10,8,6) == 240`
- `assert find_Volume(3,2,2) == 6`
- `assert find_Volume(1,2,1) == 1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 14.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_Volume(l,b,h) : 
    return ((l * b * h) / 2)
```

## Reference Implementation

```c
int mbpp_14_find_Volume(int l, int b, int h) {
    return (((l * b) * h) / 2);
}
```
