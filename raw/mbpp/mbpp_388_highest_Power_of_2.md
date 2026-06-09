# MBPP 388 Highest Power Of 2

## Problem

Write a python function to find the highest power of 2 that is less than or equal to n.

## Signature

- Python: `highest_Power_of_2(n: int) -> int`
- C entrypoint: `mbpp_388_highest_Power_of_2`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert highest_Power_of_2(10) == 8`
- `assert highest_Power_of_2(19) == 16`
- `assert highest_Power_of_2(32) == 32`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 388.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def highest_Power_of_2(n): 
    res = 0 
    for i in range(n, 0, -1): 
        if ((i & (i - 1)) == 0): 
            res = i 
            break 
    return res
```

## Reference Implementation

```c
int mbpp_388_highest_Power_of_2(int n) {
    int res = 0;
    int i;
    for (i = n; i > 0; i--) {
        if (((i & (i - 1)) == 0)) {
            res = i;
            break;
        }
    }
    return res;
}
```
