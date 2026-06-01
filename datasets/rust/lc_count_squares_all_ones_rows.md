# LC Count Square Submatrices All Ones Rows

## Problem

Return the number of square submatrices with all ones.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.

## Source

- Source: LeetCode problem `count-square-submatrices-with-all-ones`.
- URL: https://leetcode.com/problems/count-square-submatrices-with-all-ones/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_count_squares_all_ones_rows(rows: &str) -> i32 {
    let g: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let r = g.len(); let c = g[0].len(); let mut dp = vec![vec![0; c + 1]; r + 1]; let mut ans = 0; let mut i = 1usize; while i <= r { let mut j = 1usize; while j <= c { if g[i - 1][j - 1] == b'1' { dp[i][j] = 1 + dp[i - 1][j - 1].min(dp[i - 1][j].min(dp[i][j - 1])); ans += dp[i][j]; } j += 1; } i += 1; } ans
}
```
