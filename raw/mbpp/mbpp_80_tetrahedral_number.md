# MBPP 80 Tetrahedral Number

## Problem

Write a function to find the nth tetrahedral number.

## Signature

- Python: `tetrahedral_number(n: int) -> int`
- C entrypoint: `mbpp_80_tetrahedral_number`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert tetrahedral_number(5) == 35`
- `assert tetrahedral_number(6) == 56`
- `assert tetrahedral_number(7) == 84`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 80.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def tetrahedral_number(n): 
	return (n * (n + 1) * (n + 2)) / 6
```

## Reference Implementation

```c
int mbpp_80_tetrahedral_number(int n) {
    return (((n * (n + 1)) * (n + 2)) / 6);
}
```
