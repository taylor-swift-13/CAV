# MBPP 20 Is Woodall

## Problem

Write a function to check if the given number is woodball or not.

## Signature

- Python: `is_woodall(x: int) -> bool`
- C entrypoint: `mbpp_20_is_woodall`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_woodall(383) == True`
- `assert is_woodall(254) == False`
- `assert is_woodall(200) == False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 20.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_woodall(x): 
	if (x % 2 == 0): 
		return False
	if (x == 1): 
		return True
	x = x + 1 
	p = 0
	while (x % 2 == 0): 
		x = x/2
		p = p + 1
		if (p == x): 
			return True
	return False
```

## Reference Implementation

```c
int mbpp_20_is_woodall(int x) {
    if (((x % 2) == 0)) {
        return 0;
    }
    if ((x == 1)) {
        return 1;
    }
    x = (x + 1);
    int p = 0;
    while (((x % 2) == 0)) {
        x = (x / 2);
        p = (p + 1);
        if ((p == x)) {
            return 1;
        }
    }
    return 0;
}
```
