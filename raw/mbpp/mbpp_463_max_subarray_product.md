# MBPP 463 Max Subarray Product

## Problem

Write a function to find the maximum product subarray of the given array.

## Signature

- Python: `max_subarray_product(arr: List[int]) -> int`
- C entrypoint: `mbpp_463_max_subarray_product`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert max_subarray_product([1, -2, -3, 0, 7, -8, -2]) == 112`
- `assert max_subarray_product([6, -3, -10, 0, 2]) == 180`
- `assert max_subarray_product([-2, -40, 0, -2, -3]) == 80`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 463.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def max_subarray_product(arr):
	n = len(arr)
	max_ending_here = 1
	min_ending_here = 1
	max_so_far = 0
	flag = 0
	for i in range(0, n):
		if arr[i] > 0:
			max_ending_here = max_ending_here * arr[i]
			min_ending_here = min (min_ending_here * arr[i], 1)
			flag = 1
		elif arr[i] == 0:
			max_ending_here = 1
			min_ending_here = 1
		else:
			temp = max_ending_here
			max_ending_here = max (min_ending_here * arr[i], 1)
			min_ending_here = temp * arr[i]
		if (max_so_far < max_ending_here):
			max_so_far = max_ending_here
	if flag == 0 and max_so_far == 0:
		return 0
	return max_so_far
```

## Reference Implementation

```c
static int __mbpp_max_int(int a, int b) {
    if (a > b) {
        return a;
    }
    return b;
}

static int __mbpp_min_int(int a, int b) {
    if (a < b) {
        return a;
    }
    return b;
}

int mbpp_463_max_subarray_product(int *arr, int arr_size) {
    int n = arr_size;
    int max_ending_here = 1;
    int min_ending_here = 1;
    int max_so_far = 0;
    int flag = 0;
    int i;
    for (i = 0; i < n; i++) {
        if ((arr[i] > 0)) {
            max_ending_here = (max_ending_here * arr[i]);
            min_ending_here = __mbpp_min_int((min_ending_here * arr[i]), 1);
            flag = 1;
        } else {
            if ((arr[i] == 0)) {
                max_ending_here = 1;
                min_ending_here = 1;
            } else {
                int temp = max_ending_here;
                max_ending_here = __mbpp_max_int((min_ending_here * arr[i]), 1);
                min_ending_here = (temp * arr[i]);
            }
        }
        if ((max_so_far < max_ending_here)) {
            max_so_far = max_ending_here;
        }
    }
    if (((flag == 0) && (max_so_far == 0))) {
        return 0;
    }
    return max_so_far;
}
```
