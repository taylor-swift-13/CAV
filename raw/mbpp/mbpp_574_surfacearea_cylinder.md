# MBPP 574 Surfacearea Cylinder

## Problem

Write a function to find the surface area of a cylinder.

## Signature

- Python: `surfacearea_cylinder(r: int, h: int) -> float`
- C entrypoint: `mbpp_574_surfacearea_cylinder`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert surfacearea_cylinder(10,5)==942.45`
- `assert surfacearea_cylinder(4,5)==226.18800000000002`
- `assert surfacearea_cylinder(4,10)==351.848`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 574.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def surfacearea_cylinder(r,h):
  surfacearea=((2*3.1415*r*r) +(2*3.1415*r*h))
  return surfacearea
```

## Reference Implementation

```c
double mbpp_574_surfacearea_cylinder(int r, int h) {
    double surfacearea = ((((2 * 3.1415) * r) * r) + (((2 * 3.1415) * r) * h));
    return surfacearea;
}
```
