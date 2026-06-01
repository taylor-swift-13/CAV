# LC Happy Number Bool

## Problem

Return true if repeated sum-of-squares of digits reaches `1`.

## Requirements

- `n > 0`.
- Use cycle detection by the known bounded digit-square process.

## Source

- Source: LeetCode problem `happy-number`.
- URL: https://leetcode.com/problems/happy-number/
- License note: local rewrite.
- Difficulty: easy.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_happy_number_bool(mut n: i32) -> bool {
    let mut seen = vec![false; 1000]; while n != 1 && !seen[n as usize] { seen[n as usize] = true; let mut s = 0; while n > 0 { let d = n % 10; s += d * d; n /= 10; } n = s; } n == 1
}
```
