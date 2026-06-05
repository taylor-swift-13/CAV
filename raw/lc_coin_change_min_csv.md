# LC Coin Change Min CSV

## Problem

Return the fewest coins needed to make `amount`, or `-1` if impossible.

## Requirements

- `coins` is a nonempty comma-separated list of positive integers.
- `amount >= 0`.
- This is the standard unbounded coin-change objective.

## Source

- Source: LeetCode problem `coin-change`.
- URL: https://leetcode.com/problems/coin-change/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_coin_change_min_csv(const char *coins, int amount) {
    int c[128], n = 0, i = 0;
    while (coins[i] != '\0') { int v = 0; while (coins[i] >= '0' && coins[i] <= '9') { v = v * 10 + (coins[i] - '0'); i++; } c[n++] = v; if (coins[i] == ',') i++; }
    int dp[2001]; for (int j = 0; j <= amount; j++) dp[j] = 1000000; dp[0] = 0;
    for (int j = 1; j <= amount; j++) for (int k = 0; k < n; k++) if (j >= c[k] && dp[j - c[k]] + 1 < dp[j]) dp[j] = dp[j - c[k]] + 1;
    return dp[amount] >= 1000000 ? -1 : dp[amount];
}
```
