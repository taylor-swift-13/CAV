# MBPP 286 Max Sub Array Sum Repeated

## Problem

Write a function to find the largest sum of a contiguous array in the modified array which is formed by repeating the given array k times.

## Signature

- Python: `max_sub_array_sum_repeated(a: List[int], n: int, k: int) -> int`
- C entrypoint: `mbpp_286_max_sub_array_sum_repeated`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert max_sub_array_sum_repeated([10, 20, -30, -1], 4, 3) == 30`
- `assert max_sub_array_sum_repeated([-1, 10, 20], 3, 2) == 59`
- `assert max_sub_array_sum_repeated([-1, -2, -3], 3, 3) == -1`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 286.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def max_sub_array_sum_repeated(a, n, k): 
	max_so_far = -2147483648
	max_ending_here = 0
	for i in range(n*k): 
		max_ending_here = max_ending_here + a[i%n] 
		if (max_so_far < max_ending_here): 
			max_so_far = max_ending_here 
		if (max_ending_here < 0): 
			max_ending_here = 0
	return max_so_far
```

## Reference Implementation

```c
int mbpp_286_max_sub_array_sum_repeated(int *a, int a_size, int n, int k) {
    int max_so_far = (-2147483648);
    int max_ending_here = 0;
    int i;
    for (i = 0; i < (n * k); i++) {
        max_ending_here = (max_ending_here + a[(i % n)]);
        if ((max_so_far < max_ending_here)) {
            max_so_far = max_ending_here;
        }
        if ((max_ending_here < 0)) {
            max_ending_here = 0;
        }
    }
    return max_so_far;
}
```
