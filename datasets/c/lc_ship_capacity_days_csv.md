# LC Ship Capacity Within Days CSV

## Problem

Return the minimum ship capacity needed to deliver all weights within `days` days.

## Requirements

- `weights` is a comma-separated list of positive package weights.

## Source

- Source: LeetCode problem `capacity-to-ship-packages-within-d-days`.
- URL: https://leetcode.com/problems/capacity-to-ship-packages-within-d-days/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_ship_capacity_days_csv(const char *weights, int days) {
    int a[512], n = 0, i = 0, lo = 0, hi = 0; while (weights[i] != '\0') { int v = 0; while (weights[i] >= '0' && weights[i] <= '9') { v = v * 10 + weights[i] - '0'; i++; } a[n++] = v; if (v > lo) lo = v; hi += v; if (weights[i] == ',') i++; } while (lo < hi) { int mid = lo + (hi - lo) / 2, need = 1, load = 0; for (int x = 0; x < n; x++) { if (load + a[x] > mid) { need++; load = 0; } load += a[x]; } if (need <= days) hi = mid; else lo = mid + 1; } return lo;
}
```
