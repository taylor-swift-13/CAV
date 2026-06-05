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

```c
int lc_max_profit_fee_csv(const char *prices, int fee) {
    int a[512], n = 0, i = 0; while (prices[i] != '\0') { int v = 0; while (prices[i] >= '0' && prices[i] <= '9') { v = v * 10 + (prices[i] - '0'); i++; } a[n] = v; n++; if (prices[i] == ',') i++; }
    int cash = 0, hold = -a[0]; for (int k = 1; k < n; k++) { int old_cash = cash; int sell = hold + a[k] - fee; if (sell > cash) cash = sell; int buy = old_cash - a[k]; if (buy > hold) hold = buy; } return cash;
}
```
