# LC Maximal Square Area Rows

## Problem

Given binary matrix rows separated by semicolons, return the area of the largest all-1 square.

## Requirements

- Rows contain only `0` and `1`.
- All rows have the same positive length.
- The empty string returns `0`.

## Source

- Source: LeetCode problem `maximal-square`.
- URL: https://leetcode.com/problems/maximal-square/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_maximal_square_area_rows(const char *rows) {
    if (rows[0] == '\0') return 0;
    int a[64][64], r = 0, c = 0, cols = 0, i = 0;
    while (rows[i] != '\0') { c = 0; while (rows[i] == '0' || rows[i] == '1') { a[r][c] = rows[i++] - '0'; c++; } if (cols == 0) cols = c; r++; if (rows[i] == ';') i++; }
    int dp[65][65] = {{0}}, best = 0;
    for (int x = 1; x <= r; x++) for (int y = 1; y <= cols; y++) if (a[x - 1][y - 1]) { int m = dp[x - 1][y] < dp[x][y - 1] ? dp[x - 1][y] : dp[x][y - 1]; if (dp[x - 1][y - 1] < m) m = dp[x - 1][y - 1]; dp[x][y] = m + 1; if (dp[x][y] > best) best = dp[x][y]; }
    return best * best;
}
```
