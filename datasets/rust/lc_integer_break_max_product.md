# LC Integer Break Max Product

## Problem

Break `n` into at least two positive integers and return the maximum product.

## Requirements

- `2 <= n <= 58`.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `integer-break`.
- URL: https://leetcode.com/problems/integer-break/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_integer_break_max_product(n: i32) -> i32 {
    let mut dp = vec![0; (n + 1) as usize]; dp[1] = 1; let mut i = 2; while i <= n { let mut j = 1; while j < i { let a = if j > dp[j as usize] { j } else { dp[j as usize] }; let b = if i - j > dp[(i - j) as usize] { i - j } else { dp[(i - j) as usize] }; if a * b > dp[i as usize] { dp[i as usize] = a * b; } j += 1; } i += 1; } dp[n as usize]
}
```
