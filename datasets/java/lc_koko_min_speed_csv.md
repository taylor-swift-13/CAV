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

```java
class LcKokoMinSpeedCsv {
    public static int lc_koko_min_speed_csv(String piles, int h) {
        String[] parts = piles.split(",");
        int[] a = new int[parts.length];
        int max = 0;
        for (int i = 0; i < parts.length; i++) { a[i] = Integer.parseInt(parts[i]); if (a[i] > max) max = a[i]; }
        int lo = 1, hi = max;
        while (lo < hi) { int mid = lo + (hi - lo) / 2; int hours = 0; for (int v : a) hours += (v + mid - 1) / mid; if (hours <= h) hi = mid; else lo = mid + 1; }
        return lo;
    }
}
```
