# LC Coin Change II Count CSV

## Problem

Return the number of combinations that make up `amount`.

## Requirements

- `coins` is a comma-separated list of positive coin denominations.
- Coin order does not matter.

## Source

- Source: LeetCode problem `coin-change-ii`.
- URL: https://leetcode.com/problems/coin-change-ii/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_coin_change2_count_csv(int amount, const char *coins) {
    int c[128], n = 0, i = 0; while (coins[i] != '\0') { int v = 0; while (coins[i] >= '0' && coins[i] <= '9') { v = v * 10 + coins[i] - '0'; i++; } c[n++] = v; if (coins[i] == ',') i++; } int dp[2001] = {0}; dp[0] = 1; for (int k = 0; k < n; k++) for (int s = c[k]; s <= amount; s++) dp[s] += dp[s - c[k]]; return dp[amount];
}
```
