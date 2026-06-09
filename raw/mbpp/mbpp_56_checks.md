# MBPP 56 Checks

## Problem

Write a python function to check if a given number is one less than twice its reverse.

## Signature

- Python: `checks(n: int) -> bool`
- C entrypoint: `mbpp_56_checks`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert checks(70) == False`
- `assert checks(23) == False`
- `assert checks(73) == True`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 56.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def rev(num):    
    rev_num = 0
    while (num > 0):  
        rev_num = (rev_num * 10 + num % 10) 
        num = num // 10  
    return rev_num  
def checks(n):    
    return (2 * rev(n) == n + 1)
```

## Reference Implementation

```c
int rev(int num) {
    int rev_num = 0;
    while ((num > 0)) {
        rev_num = ((rev_num * 10) + (num % 10));
        num = (num / 10);
    }
    return rev_num;
}

int mbpp_56_checks(int n) {
    return ((2 * rev(n)) == (n + 1));
}
```
