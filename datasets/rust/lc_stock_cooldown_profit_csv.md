# LC Stock Cooldown Profit CSV

## Problem

Return the maximum stock profit with as many transactions as desired and a one-day cooldown after selling.

## Requirements

- `prices` is a nonempty comma-separated list of nonnegative integers.

## Source

- Source: LeetCode problem `best-time-to-buy-and-sell-stock-with-cooldown`.
- URL: https://leetcode.com/problems/best-time-to-buy-and-sell-stock-with-cooldown/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```rust
pub fn lc_stock_cooldown_profit_csv(prices: &str) -> i32 {
    let a: Vec<i32> = prices.split(',').map(|x| x.parse::<i32>().unwrap()).collect(); let mut hold = -a[0]; let mut sold = 0; let mut rest = 0;
    let mut i = 1usize; while i < a.len() { let old_hold = hold; let old_sold = sold; hold = if hold > rest - a[i] { hold } else { rest - a[i] }; sold = old_hold + a[i]; rest = if rest > old_sold { rest } else { old_sold }; i += 1; } if sold > rest { sold } else { rest }
}
```
