# best_stock_profit_csv

## Problem

Given daily prices encoded as comma-separated integers, return the maximum profit from one buy followed by one sell.

## Requirements

- Prices are nonnegative integers.
- Only one buy and one later sell are allowed.
- Return `0` if no profitable transaction exists.
- The empty string represents no prices and returns `0`.

## Source

- Source: LeetCode problem `best-time-to-buy-and-sell-stock`.
- URL: https://leetcode.com/problems/best-time-to-buy-and-sell-stock/
- License note: this is a local single-function rewrite; do not copy upstream statement text.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn best_stock_profit_csv(prices: &str) -> i32 {
    if prices.is_empty() { return 0; }
    let mut minp = 0; let mut best = 0; let mut seen = false;
    for p in prices.split(',') { let v = p.parse::<i32>().unwrap(); if !seen || v < minp { minp = v; } if v - minp > best { best = v - minp; } seen = true; }
    best
}
```
