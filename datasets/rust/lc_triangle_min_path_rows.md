# LC Triangle Minimum Path Rows

## Problem

Return the minimum path sum from top to bottom in a number triangle.

## Requirements

- Rows are semicolon-separated.
- Numbers inside each row are comma-separated signed integers.

## Source

- Source: LeetCode problem `triangle`.
- URL: https://leetcode.com/problems/triangle/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_triangle_min_path_rows(rows: &str) -> i32 {
    let rs: Vec<&str> = rows.split(';').collect(); let mut dp = vec![0i32; rs.len()]; for (r, row) in rs.iter().enumerate() { let vals: Vec<i32> = row.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut j = vals.len(); while j > 0 { j -= 1; if r == 0 { dp[0] = vals[0]; } else if j == 0 { dp[j] += vals[j]; } else if j == vals.len() - 1 { dp[j] = dp[j - 1] + vals[j]; } else { dp[j] = dp[j - 1].min(dp[j]) + vals[j]; } } } *dp.iter().min().unwrap()
}
```
