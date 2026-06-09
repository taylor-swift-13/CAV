# MBPP 432 Median Trapezium

## Problem

Write a function to find the median length of a trapezium.

## Signature

- Python: `median_trapezium(base1: int, base2: int, height: int) -> float`
- C entrypoint: `mbpp_432_median_trapezium`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert median_trapezium(15,25,35)==20`
- `assert median_trapezium(10,20,30)==15`
- `assert median_trapezium(6,9,4)==7.5`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 432.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def median_trapezium(base1,base2,height):
 median = 0.5 * (base1+ base2)
 return median
```

## Reference Implementation

```c
double mbpp_432_median_trapezium(int base1, int base2, int height) {
    double median = (0.5 * (base1 + base2));
    return median;
}
```
