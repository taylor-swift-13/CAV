# MBPP 452 Loss Amount

## Problem

Write a function that gives loss amount on a sale if the given amount has loss else return 0.

## Signature

- Python: `loss_amount(actual_cost: int, sale_amount: int) -> int`
- C entrypoint: `mbpp_452_loss_amount`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert loss_amount(1500,1200)==0`
- `assert loss_amount(100,200)==100`
- `assert loss_amount(2000,5000)==3000`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 452.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def loss_amount(actual_cost,sale_amount): 
  if(sale_amount > actual_cost):
    amount = sale_amount - actual_cost
    return amount
  else:
    return 0
```

## Reference Implementation

```c
int mbpp_452_loss_amount(int actual_cost, int sale_amount) {
    if ((sale_amount > actual_cost)) {
        int amount = (sale_amount - actual_cost);
        return amount;
    } else {
        return 0;
    }
}
```
