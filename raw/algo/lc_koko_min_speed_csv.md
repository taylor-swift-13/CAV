# LC Koko Minimum Speed CSV

## Problem

Return the minimum integer banana-eating speed needed to finish all piles within `h` hours.

## Requirements

- `piles` is a nonempty comma-separated list of positive integers.
- `h` is at least the number of piles.

## Source

- Source: LeetCode problem `koko-eating-bananas`.
- URL: https://leetcode.com/problems/koko-eating-bananas/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```c
int lc_koko_min_speed_csv(const char *piles, int h) {
    int a[128], n = 0, i = 0, max = 0;
    while (piles[i] != '\0') { int v = 0; while (piles[i] >= '0' && piles[i] <= '9') { v = v * 10 + (piles[i] - '0'); i++; } a[n] = v; n++; if (v > max) max = v; if (piles[i] == ',') i++; }
    int lo = 1, hi = max;
    while (lo < hi) { int mid = lo + (hi - lo) / 2; int hours = 0; for (int j = 0; j < n; j++) hours += (a[j] + mid - 1) / mid; if (hours <= h) hi = mid; else lo = mid + 1; }
    return lo;
}
```
