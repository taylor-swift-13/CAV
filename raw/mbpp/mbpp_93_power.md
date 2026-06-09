# MBPP 93 Power

## Problem

Write a function to calculate the value of 'a' to the power 'b'.

## Signature

- Python: `power(a: int, b: int) -> int`
- C entrypoint: `mbpp_93_power`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert power(3,4) == 81`
- `assert power(2,3) == 8`
- `assert power(5,5) == 3125`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 93.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def power(a,b):
	if b==0:
		return 1
	elif a==0:
		return 0
	elif b==1:
		return a
	else:
		return a*power(a,b-1)
```

## Reference Implementation

```c
int mbpp_93_power(int a, int b) {
    if ((b == 0)) {
        return 1;
    } else {
        if ((a == 0)) {
            return 0;
        } else {
            if ((b == 1)) {
                return a;
            } else {
                return (a * mbpp_93_power(a, (b - 1)));
            }
        }
    }
}
```
