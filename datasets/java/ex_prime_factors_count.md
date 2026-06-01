# Exercism Prime Factors Count

## Problem

Return the number of prime factors of `n`, counted with multiplicity.

## Requirements

- `n >= 1`.

## Source

- Source: Exercism problem `prime-factors`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/prime-factors
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class ExPrimeFactorsCount {
    public static int ex_prime_factors_count(int n) {
        int count = 0;
        for (int d = 2; d * d <= n; d++) while (n % d == 0) { count++; n /= d; }
        if (n > 1) count++;
        return count;
    }
}
```
