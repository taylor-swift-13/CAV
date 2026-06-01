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

```java
class LcCoinChange2CountCsv {
    public static int lc_coin_change2_count_csv(int amount, String coins) {
        String[] p = coins.split(","); int[] dp = new int[amount + 1]; dp[0] = 1; for (String part : p) { int coin = Integer.parseInt(part); for (int s = coin; s <= amount; s++) dp[s] += dp[s - coin]; } return dp[amount];
    }
}
```
