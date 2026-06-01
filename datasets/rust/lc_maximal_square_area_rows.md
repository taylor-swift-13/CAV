# LC Maximal Square Area Rows

## Problem

Given binary matrix rows separated by semicolons, return the area of the largest all-1 square.

## Requirements

- Rows contain only `0` and `1`.
- All rows have the same positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `maximal-square`.
- URL: https://leetcode.com/problems/maximal-square/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_maximal_square_area_rows(rows: &str) -> i32 {
    if rows.is_empty() { return 0; }
    let rs: Vec<&[u8]> = rows.split(';').map(|s| s.as_bytes()).collect(); let r = rs.len(); let c = rs[0].len(); let mut dp = vec![vec![0i32; c + 1]; r + 1]; let mut best = 0;
    let mut i = 1usize; while i <= r { let mut j = 1usize; while j <= c { if rs[i - 1][j - 1] == b'1' { let mut m = if dp[i - 1][j] < dp[i][j - 1] { dp[i - 1][j] } else { dp[i][j - 1] }; if dp[i - 1][j - 1] < m { m = dp[i - 1][j - 1]; } dp[i][j] = m + 1; if dp[i][j] > best { best = dp[i][j]; } } j += 1; } i += 1; }
    best * best
}
```
