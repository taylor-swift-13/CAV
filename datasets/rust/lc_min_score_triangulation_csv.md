# LC Minimum Score Triangulation CSV

## Problem

Return the minimum triangulation score for a convex polygon.

## Requirements

- `values` is a comma-separated list of vertex values.

## Source

- Source: LeetCode problem `minimum-score-triangulation-of-polygon`.
- URL: https://leetcode.com/problems/minimum-score-triangulation-of-polygon/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_score_triangulation_csv(values: &str) -> i32 {
    let a: Vec<i32> = values.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let n = a.len(); let mut dp = vec![vec![0; n]; n]; let mut len = 3usize; while len <= n { let mut l = 0usize; while l + len <= n { let r = l + len - 1; dp[l][r] = 1000000000; let mut k = l + 1; while k < r { let val = dp[l][k] + dp[k][r] + a[l] * a[k] * a[r]; if val < dp[l][r] { dp[l][r] = val; } k += 1; } l += 1; } len += 1; } dp[0][n - 1]
}
```
