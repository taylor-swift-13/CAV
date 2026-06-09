# MBPP 406 Find Parity

## Problem

Write a python function to find whether the parity of a given number is odd.

## Signature

- Python: `find_Parity(x: int) -> bool`
- C entrypoint: `mbpp_406_find_Parity`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert find_Parity(12) == False`
- `assert find_Parity(7) == True`
- `assert find_Parity(10) == False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 406.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def find_Parity(x): 
    y = x ^ (x >> 1); 
    y = y ^ (y >> 2); 
    y = y ^ (y >> 4); 
    y = y ^ (y >> 8); 
    y = y ^ (y >> 16); 
    if (y & 1): 
        return True
    return False
```

## Reference Implementation

```c
int mbpp_406_find_Parity(int x) {
    int y = (x ^ (x >> 1));
    y = (y ^ (y >> 2));
    y = (y ^ (y >> 4));
    y = (y ^ (y >> 8));
    y = (y ^ (y >> 16));
    if ((y & 1)) {
        return 1;
    }
    return 0;
}
```
