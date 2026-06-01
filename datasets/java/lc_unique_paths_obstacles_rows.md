# LC Unique Paths II Rows

## Problem

Return the number of paths from top-left to bottom-right while avoiding obstacles.

## Requirements

- Rows are semicolon-separated strings of `0` and `1`.
- `1` marks an obstacle.

## Source

- Source: LeetCode problem `unique-paths-ii`.
- URL: https://leetcode.com/problems/unique-paths-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcUniquePathsObstaclesRows {
    public static int lc_unique_paths_obstacles_rows(String rows) {
        String[] rs = rows.split(";"); int[] dp = new int[rs[0].length()]; dp[0] = 1; for (String row : rs) { for (int c = 0; c < row.length(); c++) { if (row.charAt(c) == '1') dp[c] = 0; else if (c > 0) dp[c] += dp[c - 1]; } } return dp[dp.length - 1];
    }
}
```
