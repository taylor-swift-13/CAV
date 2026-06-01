# LC Burst Balloons Max Coins CSV

## Problem

Return the maximum coins obtainable by bursting balloons optimally.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `burst-balloons`.
- URL: https://leetcode.com/problems/burst-balloons/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_burst_balloons_max_coins_csv(nums: &str) -> i32 {
    let mut a = vec![1]; for p in nums.split(',') { a.push(p.parse::<i32>().unwrap()); } a.push(1); let n = a.len(); let mut dp = vec![vec![0; n]; n]; let mut len = 2usize; while len < n { let mut l = 0usize; while l + len < n { let r = l + len; let mut k = l + 1; while k < r { let val = dp[l][k] + dp[k][r] + a[l] * a[k] * a[r]; if val > dp[l][r] { dp[l][r] = val; } k += 1; } l += 1; } len += 1; } dp[0][n - 1]
}
```
