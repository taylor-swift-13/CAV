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

```java
class LcMaxProfitFeeCsv {
    public static int lc_max_profit_fee_csv(String prices, int fee) {
        String[] p = prices.split(","); int cash = 0, hold = -Integer.parseInt(p[0]); for (int i = 1; i < p.length; i++) { int price = Integer.parseInt(p[i]); int oldCash = cash; cash = Math.max(cash, hold + price - fee); hold = Math.max(hold, oldCash - price); } return cash;
    }
}
```
