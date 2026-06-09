# MBPP 260 Newman Prime

## Problem

Write a function to find the nth newman–shanks–williams prime number.

## Signature

- Python: `newman_prime(n: int) -> int`
- C entrypoint: `mbpp_260_newman_prime`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert newman_prime(3) == 7`
- `assert newman_prime(4) == 17`
- `assert newman_prime(5) == 41`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 260.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def newman_prime(n): 
	if n == 0 or n == 1: 
		return 1
	return 2 * newman_prime(n - 1) + newman_prime(n - 2)
```

## Reference Implementation

```c
int mbpp_260_newman_prime(int n) {
    if (((n == 0) || (n == 1))) {
        return 1;
    }
    return ((2 * mbpp_260_newman_prime((n - 1))) + mbpp_260_newman_prime((n - 2)));
}
```
