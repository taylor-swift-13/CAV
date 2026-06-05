# Exercism Armstrong Number Bool

## Problem

Return true if `n` is an Armstrong number.

## Requirements

- `n >= 0`.
- Use the decimal digit count as the exponent.

## Source

- Source: Exercism problem `armstrong-numbers`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/armstrong-numbers
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_armstrong_number_bool(int n) {
    int tmp = n, digits = 0; if (tmp == 0) digits = 1; while (tmp > 0) { digits++; tmp /= 10; }
    tmp = n; int sum = 0; if (tmp == 0) sum = 0;
    while (tmp > 0) { int d = tmp % 10, p = 1; for (int i = 0; i < digits; i++) p *= d; sum += p; tmp /= 10; }
    return sum == n;
}
```
