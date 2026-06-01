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

```java
class LcMinFallingPathSumRows {
    public static int lc_min_falling_path_sum_rows(String rows) {
        String[] rs = rows.split(";"); int n = rs.length; int[][] a = new int[n][]; for (int i = 0; i < n; i++) { String[] p = rs[i].split(","); a[i] = new int[p.length]; for (int j = 0; j < p.length; j++) a[i][j] = Integer.parseInt(p[j]); } int[] dp = a[0].clone(); for (int r = 1; r < n; r++) { int[] next = new int[dp.length]; for (int c = 0; c < dp.length; c++) { int best = dp[c]; if (c > 0) best = Math.min(best, dp[c - 1]); if (c + 1 < dp.length) best = Math.min(best, dp[c + 1]); next[c] = best + a[r][c]; } dp = next; } int ans = dp[0]; for (int v : dp) ans = Math.min(ans, v); return ans;
    }
}
```
