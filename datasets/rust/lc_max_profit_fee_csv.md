# LC Stock Profit With Fee CSV

## Problem

Return the maximum profit from unlimited transactions with a fixed transaction fee.

## Requirements

- `prices` is a nonempty comma-separated list of positive integers.
- `fee >= 0`.

## Source

- Source: LeetCode problem `best-time-to-buy-and-sell-stock-with-transaction-fee`.
- URL: https://leetcode.com/problems/best-time-to-buy-and-sell-stock-with-transaction-fee/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_max_profit_fee_csv(prices: &str, fee: i32) -> i32 {
    let a: Vec<i32> = prices.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut cash = 0; let mut hold = -a[0]; let mut i = 1usize; while i < a.len() { let old_cash = cash; cash = cash.max(hold + a[i] - fee); hold = hold.max(old_cash - a[i]); i += 1; } cash
}
```
