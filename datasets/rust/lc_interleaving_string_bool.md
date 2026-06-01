# LC Interleaving String Bool

## Problem

Return true if `s3` is an interleaving of `s1` and `s2`.

## Requirements

- Character order from each source string must be preserved.

## Source

- Source: LeetCode problem `interleaving-string`.
- URL: https://leetcode.com/problems/interleaving-string/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_interleaving_string_bool(s1: &str, s2: &str, s3: &str) -> bool {
    let a = s1.as_bytes(); let b = s2.as_bytes(); let c = s3.as_bytes(); if a.len() + b.len() != c.len() { return false; } let mut dp = vec![vec![false; b.len() + 1]; a.len() + 1]; dp[0][0] = true; let mut i = 0usize; while i <= a.len() { let mut j = 0usize; while j <= b.len() { if i > 0 && dp[i - 1][j] && a[i - 1] == c[i + j - 1] { dp[i][j] = true; } if j > 0 && dp[i][j - 1] && b[j - 1] == c[i + j - 1] { dp[i][j] = true; } j += 1; } i += 1; } dp[a.len()][b.len()]
}
```
