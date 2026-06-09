# MBPP 430 Parabola Directrix

## Problem

Write a function to find the directrix of a parabola.

## Signature

- Python: `parabola_directrix(a: int, b: int, c: int) -> int`
- C entrypoint: `mbpp_430_parabola_directrix`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert parabola_directrix(5,3,2)==-198`
- `assert parabola_directrix(9,8,4)==-2336`
- `assert parabola_directrix(2,4,6)==-130`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 430.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def parabola_directrix(a, b, c): 
  directrix=((int)(c - ((b * b) + 1) * 4 * a ))
  return directrix
```

## Reference Implementation

```c
int mbpp_430_parabola_directrix(int a, int b, int c) {
    int directrix = ((int)((c - ((((b * b) + 1) * 4) * a))));
    return directrix;
}
```
