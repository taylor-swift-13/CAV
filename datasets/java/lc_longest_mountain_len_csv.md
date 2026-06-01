# LC Longest Mountain Length CSV

## Problem

Return the length of the longest mountain subarray.

## Requirements

- A mountain strictly increases then strictly decreases and has length at least 3.

## Source

- Source: LeetCode problem `longest-mountain-in-array`.
- URL: https://leetcode.com/problems/longest-mountain-in-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcLongestMountainLenCsv {
    public static int lc_longest_mountain_len_csv(String arr) {
        String[] p = arr.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int best = 0; for (int peak = 1; peak + 1 < a.length; peak++) if (a[peak - 1] < a[peak] && a[peak] > a[peak + 1]) { int l = peak, r = peak; while (l > 0 && a[l - 1] < a[l]) l--; while (r + 1 < a.length && a[r] > a[r + 1]) r++; best = Math.max(best, r - l + 1); } return best;
    }
}
```
