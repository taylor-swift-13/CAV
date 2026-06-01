# LC Longest Increasing Subsequence Length CSV

## Problem

Return the length of the longest strictly increasing subsequence in comma-separated integers.

## Requirements

- `nums` is nonempty.
- The answer fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `longest-increasing-subsequence`.
- URL: https://leetcode.com/problems/longest-increasing-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_lis_length_csv(nums: &str) -> i32 {
    let a: Vec<i32> = nums.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let mut dp = vec![1; n]; let mut best = 1;
    let mut i = 0usize; while i < n { let mut j = 0usize; while j < i { if a[j] < a[i] && dp[j] + 1 > dp[i] { dp[i] = dp[j] + 1; } j += 1; } if dp[i] > best { best = dp[i]; } i += 1; }
    best
}
```
