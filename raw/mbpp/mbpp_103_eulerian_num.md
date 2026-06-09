# MBPP 103 Eulerian Num

## Problem

Write a function to find the Eulerian number a(n, m).

## Signature

- Python: `eulerian_num(n: int, m: int) -> int`
- C entrypoint: `mbpp_103_eulerian_num`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert eulerian_num(3, 1) == 4`
- `assert eulerian_num(4, 1) == 11`
- `assert eulerian_num(5, 3) == 26`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 103.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def eulerian_num(n, m): 
	if (m >= n or n == 0): 
		return 0 
	if (m == 0): 
		return 1 
	return ((n - m) * eulerian_num(n - 1, m - 1) +(m + 1) * eulerian_num(n - 1, m))
```

## Reference Implementation

```c
int mbpp_103_eulerian_num(int n, int m) {
    if (((m >= n) || (n == 0))) {
        return 0;
    }
    if ((m == 0)) {
        return 1;
    }
    return (((n - m) * mbpp_103_eulerian_num((n - 1), (m - 1))) + ((m + 1) * mbpp_103_eulerian_num((n - 1), m)));
}
```
