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

```java
class LcCoinChangeMinCsv {
    public static int lc_coin_change_min_csv(String coins, int amount) {
        String[] parts = coins.split(","); int[] c = new int[parts.length]; for (int i = 0; i < parts.length; i++) c[i] = Integer.parseInt(parts[i]);
        int[] dp = new int[amount + 1]; for (int i = 1; i <= amount; i++) dp[i] = 1000000;
        for (int i = 1; i <= amount; i++) for (int coin : c) if (i >= coin && dp[i - coin] + 1 < dp[i]) dp[i] = dp[i - coin] + 1;
        return dp[amount] >= 1000000 ? -1 : dp[amount];
    }
}
```
