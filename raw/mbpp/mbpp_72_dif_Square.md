# MBPP 72 Dif Square

## Problem

Write a python function to check whether the given number can be represented as the difference of two squares or not.

## Signature

- Python: `dif_Square(n: int) -> bool`
- C entrypoint: `mbpp_72_dif_Square`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert dif_Square(5) == True`
- `assert dif_Square(10) == False`
- `assert dif_Square(15) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 72.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def dif_Square(n): 
    if (n % 4 != 2): 
        return True
    return False
```

## Reference Implementation

```c
int mbpp_72_dif_Square(int n) {
    if (((n % 4) != 2)) {
        return 1;
    }
    return 0;
}
```
