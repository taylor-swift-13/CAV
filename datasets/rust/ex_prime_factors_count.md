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

```rust
pub fn ex_prime_factors_count(mut n: i32) -> i32 {
    let mut count = 0; let mut d = 2;
    while d * d <= n { while n % d == 0 { count += 1; n /= d; } d += 1; }
    if n > 1 { count += 1; }
    count
}
```
