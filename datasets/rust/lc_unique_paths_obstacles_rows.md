# LC Unique Paths II Rows

## Problem

Return the number of paths from top-left to bottom-right while avoiding obstacles.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `1` marks an obstacle.

## Source

- Source: LeetCode problem `unique-paths-ii`.
- URL: https://leetcode.com/problems/unique-paths-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_unique_paths_obstacles_rows(rows: &str) -> i32 {
    let mut dp = vec![0i32; rows.split(';').next().unwrap().len()]; dp[0] = 1; for row in rows.split(';') { for (c, b) in row.bytes().enumerate() { if b == b'1' { dp[c] = 0; } else if c > 0 { dp[c] += dp[c - 1]; } } } *dp.last().unwrap()
}
```
