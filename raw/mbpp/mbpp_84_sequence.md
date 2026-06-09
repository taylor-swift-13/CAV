# MBPP 84 Sequence

## Problem

Write a function to find the nth number in the newman conway sequence.

## Signature

- Python: `sequence(n: int) -> int`
- C entrypoint: `mbpp_84_sequence`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sequence(10) == 6`
- `assert sequence(2) == 1`
- `assert sequence(3) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 84.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sequence(n): 
	if n == 1 or n == 2: 
		return 1
	else: 
		return sequence(sequence(n-1)) + sequence(n-sequence(n-1))
```

## Reference Implementation

```c
int mbpp_84_sequence(int n) {
    if (((n == 1) || (n == 2))) {
        return 1;
    } else {
        return (mbpp_84_sequence(mbpp_84_sequence((n - 1))) + mbpp_84_sequence((n - mbpp_84_sequence((n - 1)))));
    }
}
```
