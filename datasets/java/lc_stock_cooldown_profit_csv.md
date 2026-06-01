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

```java
class LcStockCooldownProfitCsv {
    public static int lc_stock_cooldown_profit_csv(String prices) {
        String[] p = prices.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int hold = -a[0], sold = 0, rest = 0;
        for (int i = 1; i < a.length; i++) { int oldHold = hold, oldSold = sold; hold = Math.max(hold, rest - a[i]); sold = oldHold + a[i]; rest = Math.max(rest, oldSold); } return Math.max(sold, rest);
    }
}
```
