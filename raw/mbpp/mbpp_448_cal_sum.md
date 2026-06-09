# MBPP 448 Cal Sum

## Problem

Write a function to calculate the sum of perrin numbers.

## Signature

- Python: `cal_sum(n: int) -> int`
- C entrypoint: `mbpp_448_cal_sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert cal_sum(9) == 49`
- `assert cal_sum(10) == 66`
- `assert cal_sum(11) == 88`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 448.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def cal_sum(n): 
	a = 3
	b = 0
	c = 2
	if (n == 0): 
		return 3
	if (n == 1): 
		return 3
	if (n == 2): 
		return 5
	sum = 5
	while (n > 2): 
		d = a + b 
		sum = sum + d 
		a = b 
		b = c 
		c = d 
		n = n-1
	return sum
```

## Reference Implementation

```c
int mbpp_448_cal_sum(int n) {
    int a = 3;
    int b = 0;
    int c = 2;
    if ((n == 0)) {
        return 3;
    }
    if ((n == 1)) {
        return 3;
    }
    if ((n == 2)) {
        return 5;
    }
    int sum = 5;
    while ((n > 2)) {
        int d = (a + b);
        sum = (sum + d);
        a = b;
        b = c;
        c = d;
        n = (n - 1);
    }
    return sum;
}
```
