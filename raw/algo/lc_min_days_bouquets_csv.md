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

```c
int lc_min_days_bouquets_csv(const char *bloom_day, int m, int k) {
    int a[512], n = 0, i = 0, lo = 1000000000, hi = 0; while (bloom_day[i] != '\0') { int v = 0; while (bloom_day[i] >= '0' && bloom_day[i] <= '9') { v = v * 10 + (bloom_day[i] - '0'); i++; } a[n] = v; n++; if (v < lo) lo = v; if (v > hi) hi = v; if (bloom_day[i] == ',') i++; } if (m * k > n) return -1; while (lo < hi) { int mid = lo + (hi - lo) / 2, made = 0, run = 0; for (int x = 0; x < n; x++) { if (a[x] <= mid) { run++; if (run == k) { made++; run = 0; } } else run = 0; } if (made >= m) hi = mid; else lo = mid + 1; } return lo;
}
```
