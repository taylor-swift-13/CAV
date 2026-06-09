# MBPP 577 Last Digit Factorial

## Problem

Write a python function to find the last digit in factorial of a given number.

## Signature

- Python: `last_Digit_Factorial(n: int) -> int`
- C entrypoint: `mbpp_577_last_Digit_Factorial`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert last_Digit_Factorial(4) == 4`
- `assert last_Digit_Factorial(21) == 0`
- `assert last_Digit_Factorial(30) == 0`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 577.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def last_Digit_Factorial(n): 
    if (n == 0): return 1
    elif (n <= 2): return n  
    elif (n == 3): return 6
    elif (n == 4): return 4 
    else: 
      return 0
```

## Reference Implementation

```c
int mbpp_577_last_Digit_Factorial(int n) {
    if ((n == 0)) {
        return 1;
    } else {
        if ((n <= 2)) {
            return n;
        } else {
            if ((n == 3)) {
                return 6;
            } else {
                if ((n == 4)) {
                    return 4;
                } else {
                    return 0;
                }
            }
        }
    }
}
```
