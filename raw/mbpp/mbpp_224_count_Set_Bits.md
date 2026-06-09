# MBPP 224 Count Set Bits

## Problem

Write a python function to count the number of set bits (binary digits with value 1) in a given number.

## Signature

- Python: `count_Set_Bits(n: int) -> int`
- C entrypoint: `mbpp_224_count_Set_Bits`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert count_Set_Bits(2) == 1`
- `assert count_Set_Bits(4) == 1`
- `assert count_Set_Bits(6) == 2`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 224.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def count_Set_Bits(n): 
    count = 0
    while (n): 
        count += n & 1
        n >>= 1
    return count
```

## Reference Implementation

```c
int mbpp_224_count_Set_Bits(int n) {
    int count = 0;
    while (n) {
        count += (n & 1);
        n >>= 1;
    }
    return count;
}
```
