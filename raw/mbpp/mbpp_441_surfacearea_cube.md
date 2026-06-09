# MBPP 441 Surfacearea Cube

## Problem

Write a function to find the surface area of a cube of a given size.

## Signature

- Python: `surfacearea_cube(l: int) -> int`
- C entrypoint: `mbpp_441_surfacearea_cube`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert surfacearea_cube(5)==150`
- `assert surfacearea_cube(3)==54`
- `assert surfacearea_cube(10)==600`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 441.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def surfacearea_cube(l):
  surfacearea= 6*l*l
  return surfacearea
```

## Reference Implementation

```c
int mbpp_441_surfacearea_cube(int l) {
    int surfacearea = ((6 * l) * l);
    return surfacearea;
}
```
