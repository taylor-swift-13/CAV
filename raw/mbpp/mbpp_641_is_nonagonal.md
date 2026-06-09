# MBPP 641 Is Nonagonal

## Problem

Write a function to find the nth nonagonal number.

## Signature

- Python: `is_nonagonal(n: int) -> int`
- C entrypoint: `mbpp_641_is_nonagonal`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_nonagonal(10) == 325`
- `assert is_nonagonal(15) == 750`
- `assert is_nonagonal(18) == 1089`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 641.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_nonagonal(n): 
	return int(n * (7 * n - 5) / 2)
```

## Reference Implementation

```c
int mbpp_641_is_nonagonal(int n) {
    return ((int)(((n * ((7 * n) - 5)) / 2)));
}
```
