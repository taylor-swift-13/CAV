# LC Find Peak Index CSV

## Problem

Return an index `i` such that `nums[i]` is greater than its neighbors; endpoints only need their one neighbor.

## Requirements

- `nums` is nonempty.
- Adjacent values are distinct in the supplied tests.

## Source

- Source: LeetCode problem `find-peak-element`.
- URL: https://leetcode.com/problems/find-peak-element/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcFindPeakIndexCsv {
    public static int lc_find_peak_index_csv(String nums) {
        String[] p = nums.split(","); int[] a = new int[p.length]; for (int i = 0; i < p.length; i++) a[i] = Integer.parseInt(p[i]);
        int l = 0, r = a.length - 1; while (l < r) { int m = l + (r - l) / 2; if (a[m] < a[m + 1]) l = m + 1; else r = m; }
        return l;
    }
}
```
