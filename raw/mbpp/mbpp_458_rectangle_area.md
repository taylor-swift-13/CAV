# MBPP 458 Rectangle Area

## Problem

Write a function to find the area of a rectangle.

## Signature

- Python: `rectangle_area(l: int, b: int) -> int`
- C entrypoint: `mbpp_458_rectangle_area`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert rectangle_area(10,20)==200`
- `assert rectangle_area(10,5)==50`
- `assert rectangle_area(4,2)==8`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 458.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def rectangle_area(l,b):
  area=l*b
  return area
```

## Reference Implementation

```c
int mbpp_458_rectangle_area(int l, int b) {
    int area = (l * b);
    return area;
}
```
