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

```rust
pub fn lc_coin_change_min_csv(coins: &str, amount: i32) -> i32 {
    let c: Vec<i32> = coins.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut dp = vec![1000000; (amount + 1) as usize]; dp[0] = 0;
    let mut i = 1; while i <= amount { for &coin in &c { if i >= coin { let cand = dp[(i - coin) as usize] + 1; if cand < dp[i as usize] { dp[i as usize] = cand; } } } i += 1; }
    if dp[amount as usize] >= 1000000 { -1 } else { dp[amount as usize] }
}
```
