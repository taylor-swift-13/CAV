# MBPP 228 All Bits Set In The Given Range

## Problem

Write a python function to check whether all the bits are unset in the given range or not.

## Signature

- Python: `all_Bits_Set_In_The_Given_Range(n: int, l: int, r: int) -> bool`
- C entrypoint: `mbpp_228_all_Bits_Set_In_The_Given_Range`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert all_Bits_Set_In_The_Given_Range(4,1,2) == True`
- `assert all_Bits_Set_In_The_Given_Range(17,2,4) == True`
- `assert all_Bits_Set_In_The_Given_Range(39,4,6) == False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 228.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def all_Bits_Set_In_The_Given_Range(n,l,r):  
    num = (((1 << r) - 1) ^ ((1 << (l - 1)) - 1)) 
    new_num = n & num
    if (new_num == 0): 
        return True
    return False
```

## Reference Implementation

```c
int mbpp_228_all_Bits_Set_In_The_Given_Range(int n, int l, int r) {
    int num = (((1 << r) - 1) ^ ((1 << (l - 1)) - 1));
    int new_num = (n & num);
    if ((new_num == 0)) {
        return 1;
    }
    return 0;
}
```
