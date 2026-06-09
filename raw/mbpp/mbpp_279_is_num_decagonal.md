# MBPP 279 Is Num Decagonal

## Problem

Write a function to find the nth decagonal number.

## Signature

- Python: `is_num_decagonal(n: int) -> int`
- C entrypoint: `mbpp_279_is_num_decagonal`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_num_decagonal(3) == 27`
- `assert is_num_decagonal(7) == 175`
- `assert is_num_decagonal(10) == 370`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 279.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_num_decagonal(n): 
	return 4 * n * n - 3 * n
```

## Reference Implementation

```c
int mbpp_279_is_num_decagonal(int n) {
    return (((4 * n) * n) - (3 * n));
}
```
