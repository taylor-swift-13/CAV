# MBPP 234 Volume Cube

## Problem

Write a function to find the volume of a cube given its side length.

## Signature

- Python: `volume_cube(l: int) -> int`
- C entrypoint: `mbpp_234_volume_cube`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert volume_cube(3)==27`
- `assert volume_cube(2)==8`
- `assert volume_cube(5)==125`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 234.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def volume_cube(l):
  volume = l * l * l
  return volume
```

## Reference Implementation

```c
int mbpp_234_volume_cube(int l) {
    int volume = ((l * l) * l);
    return volume;
}
```
