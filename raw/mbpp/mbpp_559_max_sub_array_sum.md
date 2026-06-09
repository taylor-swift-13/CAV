# MBPP 559 Max Sub Array Sum

## Problem

Write a function to find the sum of the largest contiguous sublist in the given list.

## Signature

- Python: `max_sub_array_sum(a: List[int], size: int) -> int`
- C entrypoint: `mbpp_559_max_sub_array_sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert max_sub_array_sum([-2, -3, 4, -1, -2, 1, 5, -3], 8) == 7`
- `assert max_sub_array_sum([-3, -4, 5, -2, -3, 2, 6, -4], 8) == 8`
- `assert max_sub_array_sum([-4, -5, 6, -3, -4, 3, 7, -5], 8) == 10`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 559.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def max_sub_array_sum(a, size):
  max_so_far = 0
  max_ending_here = 0
  for i in range(0, size):
    max_ending_here = max_ending_here + a[i]
    if max_ending_here < 0:
      max_ending_here = 0
    elif (max_so_far < max_ending_here):
      max_so_far = max_ending_here
  return max_so_far
```

## Reference Implementation

```c
int mbpp_559_max_sub_array_sum(int *a, int a_size, int size) {
    int max_so_far = 0;
    int max_ending_here = 0;
    int i;
    for (i = 0; i < size; i++) {
        max_ending_here = (max_ending_here + a[i]);
        if ((max_ending_here < 0)) {
            max_ending_here = 0;
        } else {
            if ((max_so_far < max_ending_here)) {
                max_so_far = max_ending_here;
            }
        }
    }
    return max_so_far;
}
```
