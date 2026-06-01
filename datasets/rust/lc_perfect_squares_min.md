# LC Perfect Squares Min

## Problem

Return the least number of perfect squares whose sum is `n`.

## Requirements

- `1 <= n <= 2000`.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `perfect-squares`.
- URL: https://leetcode.com/problems/perfect-squares/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_perfect_squares_min(n: i32) -> i32 {
    let mut dp = vec![1000000; (n + 1) as usize]; dp[0] = 0;
    let mut i = 1; while i * i <= n { let sq = i * i; let mut s = sq; while s <= n { let cand = dp[(s - sq) as usize] + 1; if cand < dp[s as usize] { dp[s as usize] = cand; } s += 1; } i += 1; }
    dp[n as usize]
}
```
