# LC Longest Common Subsequence Length

## Problem

Return the length of the longest common subsequence of two ASCII strings.

## Requirements

- String lengths are at most `63`.
- Subsequence characters keep relative order but need not be contiguous.

## Source

- Source: LeetCode problem `longest-common-subsequence`.
- URL: https://leetcode.com/problems/longest-common-subsequence/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_lcs_length(text1: &str, text2: &str) -> i32 {
    let a = text1.as_bytes();
    let b = text2.as_bytes();
    let mut dp = [[0i32; 64]; 64];
    let mut i = 1usize;
    while i <= a.len() { let mut j = 1usize; while j <= b.len() { if a[i - 1] == b[j - 1] { dp[i][j] = dp[i - 1][j - 1] + 1; } else { dp[i][j] = if dp[i - 1][j] > dp[i][j - 1] { dp[i - 1][j] } else { dp[i][j - 1] }; } j += 1; } i += 1; }
    dp[a.len()][b.len()]
}
```
