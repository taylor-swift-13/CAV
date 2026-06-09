# MBPP 89 Closest Num

## Problem

Write a function to find the closest smaller number than n.

## Signature

- Python: `closest_num(N: int) -> int`
- C entrypoint: `mbpp_89_closest_num`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert closest_num(11) == 10`
- `assert closest_num(7) == 6`
- `assert closest_num(12) == 11`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 89.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def closest_num(N):
  return (N - 1)
```

## Reference Implementation

```c
int mbpp_89_closest_num(int N) {
    return (N - 1);
}
```
