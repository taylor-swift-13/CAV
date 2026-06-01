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

```rust
pub fn ex_sieve_prime_count(limit: i32) -> i32 {
    let mut prime = [false; 1001]; let mut i = 2; while i <= limit { prime[i as usize] = true; i += 1; }
    let mut p = 2; while p * p <= limit { if prime[p as usize] { let mut q = p * p; while q <= limit { prime[q as usize] = false; q += p; } } p += 1; }
    let mut count = 0; i = 2; while i <= limit { if prime[i as usize] { count += 1; } i += 1; }
    count
}
```
