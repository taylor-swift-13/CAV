# MBPP 171 Perimeter Pentagon

## Problem

Write a function to find the perimeter of a regular pentagon from the length of its sides.

## Signature

- Python: `perimeter_pentagon(a: int) -> int`
- C entrypoint: `mbpp_171_perimeter_pentagon`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert perimeter_pentagon(5) == 25`
- `assert perimeter_pentagon(10) == 50`
- `assert perimeter_pentagon(15) == 75`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 171.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
import math
def perimeter_pentagon(a):
  perimeter=(5*a)
  return perimeter
```

## Reference Implementation

```c
int mbpp_171_perimeter_pentagon(int a) {
    int perimeter = (5 * a);
    return perimeter;
}
```
