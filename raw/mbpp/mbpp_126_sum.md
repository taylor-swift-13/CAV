# MBPP 126 Sum

## Problem

Write a python function to find the sum of common divisors of two given numbers.

## Signature

- Python: `sum(a: int, b: int) -> int`
- C entrypoint: `mbpp_126_sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert sum(10,15) == 6`
- `assert sum(100,150) == 93`
- `assert sum(4,6) == 3`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 126.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def sum(a,b): 
    sum = 0
    for i in range (1,min(a,b)): 
        if (a % i == 0 and b % i == 0): 
            sum += i 
    return sum
```

## Reference Implementation

```c
static int __mbpp_min_int(int a, int b) {
    if (a < b) {
        return a;
    }
    return b;
}

int mbpp_126_sum(int a, int b) {
    int sum = 0;
    int i;
    for (i = 1; i < __mbpp_min_int(a, b); i++) {
        if ((((a % i) == 0) && ((b % i) == 0))) {
            sum += i;
        }
    }
    return sum;
}
```
