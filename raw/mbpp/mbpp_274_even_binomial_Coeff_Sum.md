# MBPP 274 Even Binomial Coeff Sum

## Problem

Write a python function that takes in a positive integer n and finds the sum of even index binomial coefficients.

## Signature

- Python: `even_binomial_Coeff_Sum(n: int) -> int`
- C entrypoint: `mbpp_274_even_binomial_Coeff_Sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert even_binomial_Coeff_Sum(4) == 8`
- `assert even_binomial_Coeff_Sum(6) == 32`
- `assert even_binomial_Coeff_Sum(2) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 274.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
import math  
def even_binomial_Coeff_Sum( n): 
    return (1 << (n - 1))
```

## Reference Implementation

```c
int mbpp_274_even_binomial_Coeff_Sum(int n) {
    return (1 << (n - 1));
}
```
