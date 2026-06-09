# MBPP 770 Odd Num Sum

## Problem

Write a python function to find the sum of fourth power of first n odd natural numbers.

## Signature

- Python: `odd_num_sum(n: int) -> int`
- C entrypoint: `mbpp_770_odd_num_sum`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert odd_num_sum(2) == 82`
- `assert odd_num_sum(3) == 707`
- `assert odd_num_sum(4) == 3108`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 770.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def odd_num_sum(n) : 
    j = 0
    sm = 0
    for i in range(1,n + 1) : 
        j = (2*i-1) 
        sm = sm + (j*j*j*j)   
    return sm
```

## Reference Implementation

```c
int mbpp_770_odd_num_sum(int n) {
    int j = 0;
    int sm = 0;
    int i;
    for (i = 1; i < (n + 1); i++) {
        j = ((2 * i) - 1);
        sm = (sm + (((j * j) * j) * j));
    }
    return sm;
}
```
