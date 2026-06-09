# MBPP 268 Find Star Num

## Problem

Write a function to find the n'th star number.

## Signature

- Python: `find_star_num(n: int) -> int`
- C entrypoint: `mbpp_268_find_star_num`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_star_num(3) == 37`
- `assert find_star_num(4) == 73`
- `assert find_star_num(5) == 121`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 268.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_star_num(n): 
	return (6 * n * (n - 1) + 1)
```

## Reference Implementation

```c
int mbpp_268_find_star_num(int n) {
    return (((6 * n) * (n - 1)) + 1);
}
```
