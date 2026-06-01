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

```java
class LcTriangleMinPathRows {
    public static int lc_triangle_min_path_rows(String rows) {
        String[] rs = rows.split(";"); int[] dp = new int[rs.length]; for (int r = 0; r < rs.length; r++) { String[] p = rs[r].split(","); for (int j = p.length - 1; j >= 0; j--) { int v = Integer.parseInt(p[j]); if (r == 0) dp[0] = v; else if (j == 0) dp[j] += v; else if (j == p.length - 1) dp[j] = dp[j - 1] + v; else dp[j] = Math.min(dp[j - 1], dp[j]) + v; } } int best = dp[0]; for (int i = 1; i < rs.length; i++) best = Math.min(best, dp[i]); return best;
    }
}
```
