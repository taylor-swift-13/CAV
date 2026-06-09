# MBPP 799 Left Rotate

## Problem

Write a function to that rotate left bits by d bits a given number. We assume that the number is 32 bit.

## Signature

- Python: `left_rotate(n: int, d: int) -> int`
- C entrypoint: `mbpp_799_left_rotate`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert left_rotate(16,2) == 64`
- `assert left_rotate(10,2) == 40`
- `assert left_rotate(99,3) == 792`
- `assert left_rotate(99,3) == 792`
- `assert left_rotate(0b0001,3) == 0b1000`
- `assert left_rotate(0b0101,3) == 0b101000`
- `assert left_rotate(0b11101,3) == 0b11101000`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 799.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def left_rotate(n,d):   
    INT_BITS = 32
    return (n << d)|(n >> (INT_BITS - d))
```

## Reference Implementation

```c
int mbpp_799_left_rotate(int n, int d) {
    int INT_BITS = 32;
    return ((n << d) | (n >> (INT_BITS - d)));
}
```
