# MBPP 735 Toggle Middle Bits

## Problem

Write a python function to toggle bits of the number except the first and the last bit. https://www.geeksforgeeks.org/toggle-bits-number-expect-first-last-bits/

## Signature

- Python: `toggle_middle_bits(n: int) -> int`
- C entrypoint: `mbpp_735_toggle_middle_bits`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert toggle_middle_bits(9) == 15`
- `assert toggle_middle_bits(10) == 12`
- `assert toggle_middle_bits(11) == 13`
- `assert toggle_middle_bits(0b1000001) == 0b1111111`
- `assert toggle_middle_bits(0b1001101) == 0b1110011`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 735.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def set_middle_bits(n):  
    n |= n >> 1; 
    n |= n >> 2; 
    n |= n >> 4; 
    n |= n >> 8; 
    n |= n >> 16;  
    return (n >> 1) ^ 1
def toggle_middle_bits(n): 
    if (n == 1): 
        return 1
    return n ^ set_middle_bits(n)
```

## Reference Implementation

```c
int set_middle_bits(int n) {
    n |= (n >> 1);
    n |= (n >> 2);
    n |= (n >> 4);
    n |= (n >> 8);
    n |= (n >> 16);
    return ((n >> 1) ^ 1);
}

int mbpp_735_toggle_middle_bits(int n) {
    if ((n == 1)) {
        return 1;
    }
    return (n ^ set_middle_bits(n));
}
```
