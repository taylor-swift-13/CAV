# MBPP 420 Cube Sum

## Problem

Write a python function to find the cube sum of first n even natural numbers.

## Signature

- Python: `cube_Sum(n: int) -> int`
- C entrypoint: `mbpp_420_cube_Sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert cube_Sum(2) == 72`
- `assert cube_Sum(3) == 288`
- `assert cube_Sum(4) == 800`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 420.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def cube_Sum(n): 
    sum = 0
    for i in range(1,n + 1): 
        sum += (2*i)*(2*i)*(2*i) 
    return sum
```

## Reference Implementation

```c
int mbpp_420_cube_Sum(int n) {
    int sum = 0;
    int i;
    for (i = 1; i < (n + 1); i++) {
        sum += (((2 * i) * (2 * i)) * (2 * i));
    }
    return sum;
}
```
