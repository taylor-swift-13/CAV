# LC Distinct Subsequences Count

## Problem

Return how many distinct subsequences of `s` equal `t`.

## Requirements

- Inputs are ASCII.
- The supplied counts fit in signed 32-bit range.

## Source

- Source: LeetCode problem `distinct-subsequences`.
- URL: https://leetcode.com/problems/distinct-subsequences/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_distinct_subsequences_count(s: &str, t: &str) -> i32 {
    let a = s.as_bytes(); let b = t.as_bytes(); let mut dp = vec![0i64; b.len() + 1]; dp[0] = 1; for &ch in a { let mut j = b.len(); while j > 0 { j -= 1; if ch == b[j] { dp[j + 1] += dp[j]; } } } dp[b.len()] as i32
}
```
