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

```java
class LcMaximalSquareAreaRows {
    public static int lc_maximal_square_area_rows(String rows) {
        if (rows.isEmpty()) return 0;
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(); int[][] dp = new int[r + 1][c + 1]; int best = 0;
        for (int i = 1; i <= r; i++) for (int j = 1; j <= c; j++) if (rs[i - 1].charAt(j - 1) == '1') { int m = Math.min(dp[i - 1][j], dp[i][j - 1]); m = Math.min(m, dp[i - 1][j - 1]); dp[i][j] = m + 1; if (dp[i][j] > best) best = dp[i][j]; }
        return best * best;
    }
}
```
