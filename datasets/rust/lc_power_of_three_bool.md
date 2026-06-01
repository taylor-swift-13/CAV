# LC Power Of Three Bool

## Problem

Return true if `n` is a positive power of three.

## Requirements

- `n` is a signed 32-bit integer.

## Source

- Source: LeetCode problem `power-of-three`.
- URL: https://leetcode.com/problems/power-of-three/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_power_of_three_bool(mut n: i32) -> bool {
    if n <= 0 { return false; } while n % 3 == 0 { n /= 3; } n == 1
}
```
