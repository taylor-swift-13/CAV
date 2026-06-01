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

```c
int lc_min_falling_path_sum_rows(const char *rows) {
    int a[64][64], n = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + rows[i] - '0'; i++; } a[n][c++] = sign * v; if (rows[i] == ',') i++; } if (cols == 0) cols = c; n++; if (rows[i] == ';') i++; }
    int dp[64]; for (int c = 0; c < cols; c++) dp[c] = a[0][c]; for (int r = 1; r < n; r++) { int next[64]; for (int c = 0; c < cols; c++) { int best = dp[c]; if (c > 0 && dp[c - 1] < best) best = dp[c - 1]; if (c + 1 < cols && dp[c + 1] < best) best = dp[c + 1]; next[c] = best + a[r][c]; } for (int c = 0; c < cols; c++) dp[c] = next[c]; } int ans = dp[0]; for (int c = 1; c < cols; c++) if (dp[c] < ans) ans = dp[c]; return ans;
}
```
