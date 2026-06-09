# MBPP 6 Differ At One Bit Pos

## Problem

Write a python function to check whether the two numbers differ at one bit position only or not.

## Signature

- Python: `differ_At_One_Bit_Pos(a: int, b: int) -> bool`
- C entrypoint: `mbpp_6_differ_At_One_Bit_Pos`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert differ_At_One_Bit_Pos(13,9) == True`
- `assert differ_At_One_Bit_Pos(15,8) == False`
- `assert differ_At_One_Bit_Pos(2,4) == False`
- `assert differ_At_One_Bit_Pos(2, 3) == True`
- `assert differ_At_One_Bit_Pos(5, 1) == True`
- `assert differ_At_One_Bit_Pos(1, 5) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 6.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_Power_Of_Two (x): 
    return x and (not(x & (x - 1))) 
def differ_At_One_Bit_Pos(a,b): 
    return is_Power_Of_Two(a ^ b)
```

## Reference Implementation

```c
int is_Power_Of_Two(int x) {
    return (x && (!(x & (x - 1))));
}

int mbpp_6_differ_At_One_Bit_Pos(int a, int b) {
    return is_Power_Of_Two((a ^ b));
}
```
