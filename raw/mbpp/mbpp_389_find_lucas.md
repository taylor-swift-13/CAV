# MBPP 389 Find Lucas

## Problem

Write a function to find the n'th lucas number.

## Signature

- Python: `find_lucas(n: int) -> int`
- C entrypoint: `mbpp_389_find_lucas`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_lucas(9) == 76`
- `assert find_lucas(4) == 7`
- `assert find_lucas(3) == 4`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 389.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_lucas(n): 
	if (n == 0): 
		return 2
	if (n == 1): 
		return 1
	return find_lucas(n - 1) + find_lucas(n - 2)
```

## Reference Implementation

```c
int mbpp_389_find_lucas(int n) {
    if ((n == 0)) {
        return 2;
    }
    if ((n == 1)) {
        return 1;
    }
    return (mbpp_389_find_lucas((n - 1)) + mbpp_389_find_lucas((n - 2)));
}
```
