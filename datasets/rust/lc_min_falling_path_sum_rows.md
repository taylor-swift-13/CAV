# LC Minimum Falling Path Sum Rows

## Problem

Return the minimum falling path sum in a square matrix.

## Requirements

- Rows are semicolon-separated.
- Numbers inside rows are comma-separated signed integers.

## Source

- Source: LeetCode problem `minimum-falling-path-sum`.
- URL: https://leetcode.com/problems/minimum-falling-path-sum/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_min_falling_path_sum_rows(rows: &str) -> i32 {
    let a: Vec<Vec<i32>> = rows.split(';').map(|r| r.split(',').map(|x| x.parse::<i32>().unwrap()).collect()).collect(); let mut dp = a[0].clone(); let mut r = 1usize; while r < a.len() { let mut next = vec![0; dp.len()]; let mut c = 0usize; while c < dp.len() { let mut best = dp[c]; if c > 0 && dp[c - 1] < best { best = dp[c - 1]; } if c + 1 < dp.len() && dp[c + 1] < best { best = dp[c + 1]; } next[c] = best + a[r][c]; c += 1; } dp = next; r += 1; } *dp.iter().min().unwrap()
}
```
