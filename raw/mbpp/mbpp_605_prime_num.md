# MBPP 605 Prime Num

## Problem

Write a function to check if the given integer is a prime number.

## Signature

- Python: `prime_num(num: int) -> bool`
- C entrypoint: `mbpp_605_prime_num`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert prime_num(13)==True`
- `assert prime_num(7)==True`
- `assert prime_num(-1010)==False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 605.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def prime_num(num):
  if num >=1:
   for i in range(2, num//2):
     if (num % i) == 0:
                return False
     else:
                return True
  else:
          return False
```

## Reference Implementation

```c
int mbpp_605_prime_num(int num) {
    if ((num >= 1)) {
        int i;
        for (i = 2; i < (num / 2); i++) {
            if (((num % i) == 0)) {
                return 0;
            } else {
                return 1;
            }
        }
    } else {
        return 0;
    }
}
```
