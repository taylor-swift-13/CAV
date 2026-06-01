# LC Minimum Score Triangulation CSV

## Problem

Return the minimum triangulation score for a convex polygon.

## Requirements

- `values` is a comma-separated list of vertex values.

## Source

- Source: LeetCode problem `minimum-score-triangulation-of-polygon`.
- URL: https://leetcode.com/problems/minimum-score-triangulation-of-polygon/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_min_score_triangulation_csv(const char *values) {
    int a[128], n = 0, i = 0; while (values[i] != '\0') { int v = 0; while (values[i] >= '0' && values[i] <= '9') { v = v * 10 + values[i] - '0'; i++; } a[n++] = v; if (values[i] == ',') i++; } int dp[128][128] = {{0}}; for (int len = 3; len <= n; len++) for (int l = 0; l + len <= n; l++) { int r = l + len - 1; dp[l][r] = 1000000000; for (int k = l + 1; k < r; k++) { int val = dp[l][k] + dp[k][r] + a[l] * a[k] * a[r]; if (val < dp[l][r]) dp[l][r] = val; } } return dp[0][n - 1];
}
```
