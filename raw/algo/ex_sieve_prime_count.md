# Exercism Sieve Prime Count

## Problem

Return how many primes are less than or equal to `limit` using sieve-style marking.

## Requirements

- `0 <= limit <= 1000`.

## Source

- Source: Exercism problem `sieve`.
- URL: https://github.com/exercism/problem-specifications/tree/main/exercises/sieve
- License note: MIT.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int ex_sieve_prime_count(int limit) {
    int prime[1001];
    for (int i = 0; i <= limit; i++) prime[i] = i >= 2;
    for (int p = 2; p * p <= limit; p++) if (prime[p]) for (int q = p * p; q <= limit; q += p) prime[q] = 0;
    int count = 0;
    for (int i = 2; i <= limit; i++) if (prime[i]) count++;
    return count;
}
```
