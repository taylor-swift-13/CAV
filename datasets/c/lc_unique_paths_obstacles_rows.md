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

```c
int lc_unique_paths_obstacles_rows(const char *rows) {
    int dp[64] = {0}, i = 0; dp[0] = 1;
    while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') { if (rows[i] == '1') dp[c] = 0; else if (c > 0) dp[c] += dp[c - 1]; c++; i++; } if (rows[i] == ';') i++; }
    int last = 0; while (rows[last] != '\0' && rows[last] != ';') last++; return dp[last - 1];
}
```
