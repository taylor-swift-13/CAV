# MBPP 309 Maximum

## Problem

Write a python function to find the maximum of two numbers.

## Signature

- Python: `maximum(a: int, b: int) -> int`
- C entrypoint: `mbpp_309_maximum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert maximum(5,10) == 10`
- `assert maximum(-1,-2) == -1`
- `assert maximum(9,7) == 9`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 309.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def maximum(a,b):   
    if a >= b: 
        return a 
    else: 
        return b
```

## Reference Implementation

```c
int mbpp_309_maximum(int a, int b) {
    if ((a >= b)) {
        return a;
    } else {
        return b;
    }
}
```
