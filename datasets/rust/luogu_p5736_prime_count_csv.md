# Luogu P5736 Prime Count CSV

## Problem

Return how many comma-separated integers are prime.

## Requirements

- The empty string represents an empty list.
- Values are nonnegative.

## Source

- Source: Luogu problem `P5736`.
- URL: https://www.luogu.com.cn/problem/P5736
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn luogu_p5736_prime_count_csv(nums: &str) -> i32 {
    if nums.is_empty() { return 0; }
    let mut count = 0;
    for part in nums.split(',') { let x = part.parse::<i32>().unwrap(); let mut prime = x >= 2; let mut d = 2; while d * d <= x { if x % d == 0 { prime = false; } d += 1; } if prime { count += 1; } }
    count
}
```
