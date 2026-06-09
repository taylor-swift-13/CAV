# MBPP 555 Difference

## Problem

Write a python function to find the difference between the sum of cubes of the first n natural numbers and the sum of the first n natural numbers.

## Signature

- Python: `difference(n: int) -> int`
- C entrypoint: `mbpp_555_difference`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert difference(3) == 30`
- `assert difference(5) == 210`
- `assert difference(2) == 6`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 555.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def difference(n) :  
    S = (n*(n + 1))//2;  
    res = S*(S-1);  
    return res;
```

## Reference Implementation

```c
int mbpp_555_difference(int n) {
    int S = ((n * (n + 1)) / 2);
    int res = (S * (S - 1));
    return res;
}
```
