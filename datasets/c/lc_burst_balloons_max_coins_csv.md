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

```c
int lc_burst_balloons_max_coins_csv(const char *nums) {
    int a[130], n = 1, i = 0; a[0] = 1; while (nums[i] != '\0') { int v = 0; while (nums[i] >= '0' && nums[i] <= '9') { v = v * 10 + nums[i] - '0'; i++; } a[n++] = v; if (nums[i] == ',') i++; } a[n++] = 1; int dp[130][130] = {{0}}; for (int len = 2; len < n; len++) for (int l = 0; l + len < n; l++) { int r = l + len; for (int k = l + 1; k < r; k++) { int val = dp[l][k] + dp[k][r] + a[l] * a[k] * a[r]; if (val > dp[l][r]) dp[l][r] = val; } } return dp[0][n - 1];
}
```
