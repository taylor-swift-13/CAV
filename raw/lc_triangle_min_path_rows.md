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

```c
int lc_triangle_min_path_rows(const char *rows) {
    int dp[128] = {0}, i = 0, row = 0;
    while (rows[i] != '\0') { int vals[128], c = 0; while (rows[i] != '\0' && rows[i] != ';') { int sign = 1, v = 0; if (rows[i] == '-') { sign = -1; i++; } while (rows[i] >= '0' && rows[i] <= '9') { v = v * 10 + (rows[i] - '0'); i++; } vals[c] = sign * v; c++; if (rows[i] == ',') i++; } if (row == 0) dp[0] = vals[0]; else { for (int j = c - 1; j >= 0; j--) { if (j == 0) dp[j] = dp[j] + vals[j]; else if (j == c - 1) dp[j] = dp[j - 1] + vals[j]; else dp[j] = (dp[j - 1] < dp[j] ? dp[j - 1] : dp[j]) + vals[j]; } } row++; if (rows[i] == ';') i++; }
    int best = dp[0]; for (int j = 1; j < row; j++) if (dp[j] < best) best = dp[j]; return best;
}
```
