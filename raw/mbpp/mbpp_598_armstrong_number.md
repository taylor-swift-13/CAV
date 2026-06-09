# MBPP 598 Armstrong Number

## Problem

Write a function to check whether the given number is armstrong or not.

## Signature

- Python: `armstrong_number(number: int) -> bool`
- C entrypoint: `mbpp_598_armstrong_number`
- C translation: `List[int]` parameters are represented as `int *name, int name_size`; `bool` results are represented as `int` where `0` is false and nonzero is true.

## Tests

- `assert armstrong_number(153)==True`
- `assert armstrong_number(259)==False`
- `assert armstrong_number(4458)==False`

## Source

- Source: MBPP sanitized task from local MultiPL-E benchmark sources.
- Task id: 598.
- Translation note: Python reference implementation mechanically translated to C for the scalar and `List[int]` input subset.

## Original Python Implementation

```python
def armstrong_number(number):
 sum = 0
 times = 0
 temp = number
 while temp > 0:
           times = times + 1
           temp = temp // 10
 temp = number
 while temp > 0:
           reminder = temp % 10
           sum = sum + (reminder ** times)
           temp //= 10
 if number == sum:
           return True
 else:
           return False
```

## Reference Implementation

```c
static int __mbpp_pow_int(int base, int exp) {
    int result = 1;
    while (exp > 0) {
        result = result * base;
        exp = exp - 1;
    }
    return result;
}

int mbpp_598_armstrong_number(int number) {
    int sum = 0;
    int times = 0;
    int temp = number;
    while ((temp > 0)) {
        times = (times + 1);
        temp = (temp / 10);
    }
    temp = number;
    while ((temp > 0)) {
        int reminder = (temp % 10);
        sum = (sum + __mbpp_pow_int(reminder, times));
        temp /= 10;
    }
    if ((number == sum)) {
        return 1;
    } else {
        return 0;
    }
}
```
