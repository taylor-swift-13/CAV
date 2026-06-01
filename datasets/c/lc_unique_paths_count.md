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

```c
int lc_unique_paths_count(int m, int n) {
    int dp[31][31];
    for (int i = 0; i < m; i++) dp[i][0] = 1;
    for (int j = 0; j < n; j++) dp[0][j] = 1;
    for (int i = 1; i < m; i++) for (int j = 1; j < n; j++) dp[i][j] = dp[i - 1][j] + dp[i][j - 1];
    return dp[m - 1][n - 1];
}
```
