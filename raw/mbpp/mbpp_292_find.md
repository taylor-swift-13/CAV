# MBPP 292 Find

## Problem

Write a python function to find quotient of two numbers (rounded down to the nearest integer).

## Signature

- Python: `find(n: int, m: int) -> int`
- C entrypoint: `mbpp_292_find`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find(10,3) == 3`
- `assert find(4,2) == 2`
- `assert find(20,5) == 4`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 292.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find(n,m):  
    q = n//m 
    return (q)
```

## Reference Implementation

```c
int mbpp_292_find(int n, int m) {
    int q = (n / m);
    return q;
}
```
