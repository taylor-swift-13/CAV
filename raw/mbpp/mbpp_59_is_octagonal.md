# MBPP 59 Is Octagonal

## Problem

Write a function to find the nth octagonal number.

## Signature

- Python: `is_octagonal(n: int) -> int`
- C entrypoint: `mbpp_59_is_octagonal`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_octagonal(5) == 65`
- `assert is_octagonal(10) == 280`
- `assert is_octagonal(15) == 645`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 59.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_octagonal(n): 
	return 3 * n * n - 2 * n
```

## Reference Implementation

```c
int mbpp_59_is_octagonal(int n) {
    return (((3 * n) * n) - (2 * n));
}
```
