# MBPP 17 Square Perimeter

## Problem

Write a function that returns the perimeter of a square given its side length as input.

## Signature

- Python: `square_perimeter(a: int) -> int`
- C entrypoint: `mbpp_17_square_perimeter`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert square_perimeter(10)==40`
- `assert square_perimeter(5)==20`
- `assert square_perimeter(4)==16`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 17.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def square_perimeter(a):
  perimeter=4*a
  return perimeter
```

## Reference Implementation

```c
int mbpp_17_square_perimeter(int a) {
    int perimeter = (4 * a);
    return perimeter;
}
```
