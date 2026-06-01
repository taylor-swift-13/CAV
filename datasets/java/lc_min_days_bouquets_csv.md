# LC Minimum Days Bouquets CSV

## Problem

Return the minimum day needed to make `m` bouquets of `k` adjacent flowers, or `-1` if impossible.

## Requirements

- `bloom_day` is a comma-separated list of positive days.

## Source

- Source: LeetCode problem `minimum-number-of-days-to-make-m-bouquets`.
- URL: https://leetcode.com/problems/minimum-number-of-days-to-make-m-bouquets/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcMinDaysBouquetsCsv {
    public static int lc_min_days_bouquets_csv(String bloom_day, int m, int k) {
        String[] p = bloom_day.split(","); int[] a = new int[p.length]; int lo = 1000000000, hi = 0; for (int i = 0; i < p.length; i++) { a[i] = Integer.parseInt(p[i]); lo = Math.min(lo, a[i]); hi = Math.max(hi, a[i]); } if (m * k > a.length) return -1; while (lo < hi) { int mid = lo + (hi - lo) / 2, made = 0, run = 0; for (int v : a) { if (v <= mid) { if (++run == k) { made++; run = 0; } } else run = 0; } if (made >= m) hi = mid; else lo = mid + 1; } return lo;
    }
}
```
