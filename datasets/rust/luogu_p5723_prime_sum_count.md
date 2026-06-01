# Luogu P5723 Prime Sum Count

## Problem

Return how many consecutive primes starting from `2` can be added without the sum exceeding `limit`.

## Requirements

- `limit >= 0`.
- Primes are considered in increasing order.

## Source

- Source: Luogu problem `P5723`.
- URL: https://www.luogu.com.cn/problem/P5723
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5723_prime_sum_count(limit: i32) -> i32 {
    let mut sum = 0; let mut count = 0; let mut x = 2;
    while x <= limit { let mut prime = true; let mut d = 2; while d * d <= x { if x % d == 0 { prime = false; } d += 1; } if prime { if sum + x > limit { break; } sum += x; count += 1; } x += 1; }
    count
}
```
