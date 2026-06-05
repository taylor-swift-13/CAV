# Exercism Nth Prime Value

## Problem

Return the `n`th prime number using one-based indexing.

## Requirements

- `n >= 1`.
- The answer fits in signed 32-bit integer range.

## Source

- Source: Exercism problem `nth-prime`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/nth-prime
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_nth_prime_value(int n) {
    int count = 0;
    for (int x = 2;; x++) { int prime = 1; for (int d = 2; d * d <= x; d++) if (x % d == 0) prime = 0; if (prime && ++count == n) return x; }
}
```
