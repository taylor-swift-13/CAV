# MBPP 138 Is Sum Of Powers Of Two

## Problem

Write a python function to check whether the given number can be represented as sum of non-zero powers of 2 or not.

## Signature

- Python: `is_Sum_Of_Powers_Of_Two(n: int) -> bool`
- C entrypoint: `mbpp_138_is_Sum_Of_Powers_Of_Two`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert is_Sum_Of_Powers_Of_Two(10) == True`
- `assert is_Sum_Of_Powers_Of_Two(7) == False`
- `assert is_Sum_Of_Powers_Of_Two(14) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 138.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_Sum_Of_Powers_Of_Two(n): 
    if (n % 2 == 1): 
        return False
    else: 
        return True
```

## Reference Implementation

```c
int mbpp_138_is_Sum_Of_Powers_Of_Two(int n) {
    if (((n % 2) == 1)) {
        return 0;
    } else {
        return 1;
    }
}
```
