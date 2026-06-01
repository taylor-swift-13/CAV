# LC Unique Paths Count

## Problem

Return the number of right/down paths in an `m` by `n` grid.

## Requirements

- `1 <= m, n <= 30`.
- The result fits in signed 32-bit integer range.

## Source

- Source: LeetCode problem `unique-paths`.
- URL: https://leetcode.com/problems/unique-paths/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_unique_paths_count(m: i32, n: i32) -> i32 {
    let mut dp = [[0i32; 31]; 31];
    let mut i = 0;
    while i < m { dp[i as usize][0] = 1; i += 1; }
    let mut j = 0;
    while j < n { dp[0][j as usize] = 1; j += 1; }
    i = 1;
    while i < m { j = 1; while j < n { dp[i as usize][j as usize] = dp[(i - 1) as usize][j as usize] + dp[i as usize][(j - 1) as usize]; j += 1; } i += 1; }
    dp[(m - 1) as usize][(n - 1) as usize]
}
```
