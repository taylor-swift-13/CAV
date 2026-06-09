# MBPP 86 Centered Hexagonal Number

## Problem

Write a function to find nth centered hexagonal number.

## Signature

- Python: `centered_hexagonal_number(n: int) -> int`
- C entrypoint: `mbpp_86_centered_hexagonal_number`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert centered_hexagonal_number(10) == 271`
- `assert centered_hexagonal_number(2) == 7`
- `assert centered_hexagonal_number(9) == 217`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 86.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def centered_hexagonal_number(n):
  return 3 * n * (n - 1) + 1
```

## Reference Implementation

```c
int mbpp_86_centered_hexagonal_number(int n) {
    return (((3 * n) * (n - 1)) + 1);
}
```
