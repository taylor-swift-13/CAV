# MBPP 256 Count Primes Nums

## Problem

Write a python function that takes in a non-negative number and returns the number of prime numbers less than the given non-negative number.

## Signature

- Python: `count_Primes_nums(n: int) -> int`
- C entrypoint: `mbpp_256_count_Primes_nums`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert count_Primes_nums(5) == 2`
- `assert count_Primes_nums(10) == 4`
- `assert count_Primes_nums(100) == 25`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 256.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def count_Primes_nums(n):
    ctr = 0
    for num in range(n):
        if num <= 1:
            continue
        for i in range(2,num):
            if (num % i) == 0:
                break
        else:
            ctr += 1
    return ctr
```

## Reference Implementation

```c
int mbpp_256_count_Primes_nums(int n) {
    int ctr = 0;
    int num;
    for (num = 0; num < n; num++) {
        if ((num <= 1)) {
            continue;
        }
        int i;
        for (i = 2; i < num; i++) {
            if (((num % i) == 0)) {
                break;
            }
        }
    }
    return ctr;
}
```
