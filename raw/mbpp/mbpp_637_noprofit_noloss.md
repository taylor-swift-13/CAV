# MBPP 637 Noprofit Noloss

## Problem

Write a function to check whether the given amount has no profit and no loss

## Signature

- Python: `noprofit_noloss(actual_cost: int, sale_amount: int) -> bool`
- C entrypoint: `mbpp_637_noprofit_noloss`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert noprofit_noloss(1500,1200)==False`
- `assert noprofit_noloss(100,100)==True`
- `assert noprofit_noloss(2000,5000)==False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 637.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def noprofit_noloss(actual_cost,sale_amount): 
  if(sale_amount == actual_cost):
    return True
  else:
    return False
```

## Reference Implementation

```c
int mbpp_637_noprofit_noloss(int actual_cost, int sale_amount) {
    if ((sale_amount == actual_cost)) {
        return 1;
    } else {
        return 0;
    }
}
```
