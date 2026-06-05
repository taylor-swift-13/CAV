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

```c
int best_stock_profit_csv(const char *prices) {
    int minp = 0, best = 0, seen = 0, i = 0;
    while (prices[i] != '\0') { int v = 0; while (prices[i] >= '0' && prices[i] <= '9') { v = v * 10 + prices[i] - '0'; i++; } if (!seen || v < minp) minp = v; if (v - minp > best) best = v - minp; seen = 1; if (prices[i] == ',') i++; }
    return best;
}
```
