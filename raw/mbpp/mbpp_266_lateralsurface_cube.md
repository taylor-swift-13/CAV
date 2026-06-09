# MBPP 266 Lateralsurface Cube

## Problem

Write a function to find the lateral surface area of a cube given its side length.

## Signature

- Python: `lateralsurface_cube(l: int) -> int`
- C entrypoint: `mbpp_266_lateralsurface_cube`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert lateralsurface_cube(5)==100`
- `assert lateralsurface_cube(9)==324`
- `assert lateralsurface_cube(10)==400`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 266.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def lateralsurface_cube(l):
  LSA = 4 * (l * l)
  return LSA
```

## Reference Implementation

```c
int mbpp_266_lateralsurface_cube(int l) {
    int LSA = (4 * (l * l));
    return LSA;
}
```
