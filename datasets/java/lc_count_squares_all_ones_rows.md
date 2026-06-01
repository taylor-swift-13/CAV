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

```java
class LcCountSquaresAllOnesRows {
    public static int lc_count_squares_all_ones_rows(String rows) {
        String[] rs = rows.split(";"); int r = rs.length, c = rs[0].length(), ans = 0; int[][] dp = new int[r + 1][c + 1]; for (int i = 1; i <= r; i++) for (int j = 1; j <= c; j++) if (rs[i - 1].charAt(j - 1) == '1') { dp[i][j] = 1 + Math.min(dp[i - 1][j - 1], Math.min(dp[i - 1][j], dp[i][j - 1])); ans += dp[i][j]; } return ans;
    }
}
```
