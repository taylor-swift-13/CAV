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

```c
int lc_stock_cooldown_profit_csv(const char *prices) {
    int a[256], n = 0, i = 0; while (prices[i] != '\0') { int v = 0; while (prices[i] >= '0' && prices[i] <= '9') { v = v * 10 + prices[i] - '0'; i++; } a[n++] = v; if (prices[i] == ',') i++; }
    int hold = -a[0], sold = 0, rest = 0;
    for (int d = 1; d < n; d++) { int old_hold = hold, old_sold = sold; hold = hold > rest - a[d] ? hold : rest - a[d]; sold = old_hold + a[d]; rest = rest > old_sold ? rest : old_sold; }
    return sold > rest ? sold : rest;
}
```
