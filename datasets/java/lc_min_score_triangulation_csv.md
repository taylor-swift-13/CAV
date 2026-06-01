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

```java
class LcMinScoreTriangulationCsv {
    public static int lc_min_score_triangulation_csv(String values) {
        String[] p = values.split(","); int n = p.length; int[] a = new int[n]; for (int i = 0; i < n; i++) a[i] = Integer.parseInt(p[i]); int[][] dp = new int[n][n]; for (int len = 3; len <= n; len++) for (int l = 0; l + len <= n; l++) { int r = l + len - 1; dp[l][r] = 1000000000; for (int k = l + 1; k < r; k++) dp[l][r] = Math.min(dp[l][r], dp[l][k] + dp[k][r] + a[l] * a[k] * a[r]); } return dp[0][n - 1];
    }
}
```
