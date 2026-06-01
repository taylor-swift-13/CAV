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

```rust
pub fn ex_nth_prime_value(n: i32) -> i32 {
    let mut count = 0; let mut x = 2;
    loop { let mut prime = true; let mut d = 2; while d * d <= x { if x % d == 0 { prime = false; } d += 1; } if prime { count += 1; if count == n { return x; } } x += 1; }
}
```
