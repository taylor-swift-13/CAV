# MBPP 271 Even Power Sum

## Problem

Write a python function that takes in an integer n and finds the sum of the first n even natural numbers that are raised to the fifth power.

## Signature

- Python: `even_Power_Sum(n: int) -> int`
- C entrypoint: `mbpp_271_even_Power_Sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert even_Power_Sum(2) == 1056`
- `assert even_Power_Sum(3) == 8832`
- `assert even_Power_Sum(1) == 32`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 271.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def even_Power_Sum(n): 
    sum = 0; 
    for i in range(1,n+1): 
        j = 2*i; 
        sum = sum + (j*j*j*j*j); 
    return sum;
```

## Reference Implementation

```c
int mbpp_271_even_Power_Sum(int n) {
    int sum = 0;
    int i;
    for (i = 1; i < (n + 1); i++) {
        int j = (2 * i);
        sum = (sum + ((((j * j) * j) * j) * j));
    }
    return sum;
}
```
