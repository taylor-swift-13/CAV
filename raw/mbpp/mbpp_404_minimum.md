# MBPP 404 Minimum

## Problem

Write a python function to find the minimum of two numbers.

## Signature

- Python: `minimum(a: int, b: int) -> int`
- C entrypoint: `mbpp_404_minimum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert minimum(1,2) == 1`
- `assert minimum(-5,-4) == -5`
- `assert minimum(0,0) == 0`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 404.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def minimum(a,b):   
    if a <= b: 
        return a 
    else: 
        return b
```

## Reference Implementation

```c
int mbpp_404_minimum(int a, int b) {
    if ((a <= b)) {
        return a;
    } else {
        return b;
    }
}
```
