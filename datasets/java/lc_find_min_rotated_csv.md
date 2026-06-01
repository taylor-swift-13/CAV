# LC Find Minimum In Rotated Sorted Array CSV

## Problem

Return the minimum value in a rotated sorted array with distinct integers.

## Requirements

- `nums` is a nonempty comma-separated list.
- Values are distinct.

## Source

- Source: LeetCode problem `find-minimum-in-rotated-sorted-array`.
- URL: https://leetcode.com/problems/find-minimum-in-rotated-sorted-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFindMinRotatedCsv {
    public static int lc_find_min_rotated_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]); int l = 0, r = a.length - 1; while (l < r) { int m = l + (r - l) / 2; if (a[m] > a[r]) l = m + 1; else r = m; } return a[l];
    }
}
```
