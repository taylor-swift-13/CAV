# MBPP 803 Is Perfect Square

## Problem

Write a function to check whether the given number is a perfect square or not. https://www.geeksforgeeks.org/check-if-given-number-is-perfect-square-in-cpp/

## Signature

- Python: `is_perfect_square(n: int) -> bool`
- C entrypoint: `mbpp_803_is_perfect_square`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert not is_perfect_square(10)`
- `assert is_perfect_square(36)`
- `assert not is_perfect_square(14)`
- `assert is_perfect_square(14*14)`
- `assert not is_perfect_square(125)`
- `assert is_perfect_square(125*125)`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 803.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def is_perfect_square(n) :
    i = 1
    while (i * i<= n):
        if ((n % i == 0) and (n / i == i)):
            return True     
        i = i + 1
    return False
```

## Reference Implementation

```c
int mbpp_803_is_perfect_square(int n) {
    int i = 1;
    while (((i * i) <= n)) {
        if ((((n % i) == 0) && ((n / i) == i))) {
            return 1;
        }
        i = (i + 1);
    }
    return 0;
}
```
