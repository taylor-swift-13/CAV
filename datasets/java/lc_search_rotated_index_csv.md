# LC Search Rotated Index CSV

## Problem

Return the index of `target` in a rotated sorted distinct integer array, or `-1` if absent.

## Requirements

- `nums` is comma-separated and nonempty.
- Values are distinct.

## Source

- Source: LeetCode problem `search-in-rotated-sorted-array`.
- URL: https://leetcode.com/problems/search-in-rotated-sorted-array/
- License note: local rewrite.
- Difficulty: medium.
- Style: HumanEval-like short single-function task; not HumanEval or MBPP.

## Reference Implementation

```java
class LcSearchRotatedIndexCsv {
    public static int lc_search_rotated_index_csv(String nums, int target) {
        String[] parts = nums.split(",");
        int[] a = new int[parts.length];
        for (int i = 0; i < parts.length; i++) a[i] = Integer.parseInt(parts[i]);
        int l = 0, r = a.length - 1;
        while (l <= r) { int mid = l + (r - l) / 2; if (a[mid] == target) return mid; if (a[l] <= a[mid]) { if (a[l] <= target && target < a[mid]) r = mid - 1; else l = mid + 1; } else { if (a[mid] < target && target <= a[r]) l = mid + 1; else r = mid - 1; } }
        return -1;
    }
}
```
