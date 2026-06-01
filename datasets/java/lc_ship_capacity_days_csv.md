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

```java
class LcShipCapacityDaysCsv {
    public static int lc_ship_capacity_days_csv(String weights, int days) {
        String[] p = weights.split(","); int[] a = new int[p.length]; int lo = 0, hi = 0; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); lo = Math.max(lo, a[i]); hi += a[i]; } while (lo < hi) { int mid = lo + (hi - lo) / 2, need = 1, load = 0; for (int v : a) { if (load + v > mid) { need++; load = 0; } load += v; } if (need <= days) hi = mid; else lo = mid + 1; } return lo;
    }
}
```
