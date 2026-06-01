# LC Count Square Submatrices All Ones Rows

## Problem

Return the number of square submatrices with all ones.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.

## Source

- Source: LeetCode problem `count-square-submatrices-with-all-ones`.
- URL: https://leetcode.com/problems/count-square-submatrices-with-all-ones/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_count_squares_all_ones_rows(const char *rows) {
    char g[64][64]; int r = 0, cols = 0, i = 0; while (rows[i] != '\0') { int c = 0; while (rows[i] == '0' || rows[i] == '1') g[r][c++] = rows[i++]; if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; } int dp[65][65] = {{0}}, ans = 0; for (int x = 1; x <= r; x++) for (int y = 1; y <= cols; y++) if (g[x - 1][y - 1] == '1') { int m = dp[x - 1][y] < dp[x][y - 1] ? dp[x - 1][y] : dp[x][y - 1]; if (dp[x - 1][y - 1] < m) m = dp[x - 1][y - 1]; dp[x][y] = m + 1; ans += dp[x][y]; } return ans;
}
```
