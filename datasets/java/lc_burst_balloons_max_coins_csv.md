# LC Burst Balloons Max Coins CSV

## Problem

Return the maximum coins obtainable by bursting balloons optimally.

## Requirements

- `nums` is a comma-separated list of positive integers.

## Source

- Source: LeetCode problem `burst-balloons`.
- URL: https://leetcode.com/problems/burst-balloons/
- License note: local rewrite.
- Difficulty: hard.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcBurstBalloonsMaxCoinsCsv {
    public static int lc_burst_balloons_max_coins_csv(String nums) {
        String[] p = nums.split(","); int n = p.length + 2; int[] a = new int[n]; a[0] = 1; a[n - 1] = 1; for (int i = 0; i < p.length; i++) a[i + 1] = Integer.parseInt(p[i]); int[][] dp = new int[n][n]; for (int len = 2; len < n; len++) for (int l = 0; l + len < n; l++) { int r = l + len; for (int k = l + 1; k < r; k++) dp[l][r] = Math.max(dp[l][r], dp[l][k] + dp[k][r] + a[l] * a[k] * a[r]); } return dp[0][n - 1];
    }
}
```
