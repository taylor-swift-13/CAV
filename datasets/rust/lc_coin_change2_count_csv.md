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

```rust
pub fn lc_coin_change2_count_csv(amount: i32, coins: &str) -> i32 {
    let mut dp = vec![0; (amount + 1) as usize]; dp[0] = 1; for part in coins.split(',') { let coin = part.parse::<usize>().unwrap(); let mut s = coin; while s <= amount as usize { dp[s] += dp[s - coin]; s += 1; } } dp[amount as usize]
}
```
