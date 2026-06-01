# Exercism Perfect Number Code

## Problem

Classify `n` by aliquot sum: return `1` for perfect, `2` for abundant, and `3` for deficient.

## Requirements

- `n > 0`.
- The aliquot sum is the sum of positive divisors strictly smaller than `n`.

## Source

- Source: Exercism problem `perfect-numbers`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/perfect-numbers
- License note: MIT.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExPerfectNumberCode {
    public static int ex_perfect_number_code(int n) {
        int sum = 0;
        for (int d = 1; d < n; d++) if (n % d == 0) sum += d;
        if (sum == n) return 1;
        if (sum > n) return 2;
        return 3;
    }
}
```
